import NetHack.Soko22Hazard87.AndIntroBlocks0162
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro40750 (p : Pattern) (ha : d177465 p = 1) (hb : d180267 p = 1) : d180454 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d177448 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d177393 q = 1) (hb : d178318 q = 1) : d179321 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d177393, d178318, d179321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40508 q ha hb
    | true =>
      simp only [d177393, d178318, d179321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40498 q ha hb
  have h3 (q : Pattern) (ha : d177449 q = 1) (hb : d178319 q = 1) : d179322 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d177449, d178319, d179322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d177449, d178319, d179322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d177452 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d177453 q = 1) (hb : d178320 q = 1) : d179323 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d177453, d178320, d179323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d177453, d178320, d179323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d177463 q = 1) (hb : d178321 q = 1) : d179324 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d177463, d178321, d179324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177463, d178321, d179324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d177464 q = 1) (hb : d178322 q = 1) : d179325 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d177464, d178322, d179325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177464, d178322, d179325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d177465 q = 1) (hb : d180267 q = 1) : d180454 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d177465, d180267, d180454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177465, d180267, d180454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro40751 (p : Pattern) (ha : d177507 p = 1) (hb : d180278 p = 1) : d180464 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d177495 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d177496 q = 1) (hb : d180273 q = 1) : d179440 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d177496, d180273, d179440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40534 q ha hb
    | true =>
      simp only [d177496, d180273, d179440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40503 q ha hb
  have h3 (q : Pattern) (ha : d177497 q = 1) (hb : d180274 q = 1) : d180460 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d177497, d180274, d180460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d177497, d180274, d180460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d177503 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d177504 q = 1) (hb : d180275 q = 1) : d180461 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d177504, d180275, d180461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d177504, d180275, d180461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d177505 q = 1) (hb : d180276 q = 1) : d180462 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d177505, d180276, d180462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177505, d180276, d180462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d177506 q = 1) (hb : d180277 q = 1) : d180463 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d177506, d180277, d180463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177506, d180277, d180463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d177507 q = 1) (hb : d180278 q = 1) : d180464 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d177507, d180278, d180464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177507, d180278, d180464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro40752 (p : Pattern) (ha : d177513 p = 1) (hb : d180284 p = 1) : d180470 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d177401 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d177457 q = 1) (hb : d178324 q = 1) : d179327 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d177457, d178324, d179327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40748 q ha hb
    | true =>
      simp only [d177457, d178324, d179327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40749 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d177459 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d177460 q = 1) (hb : d178325 q = 1) : d179328 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d177460, d178325, d179328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d177460, d178325, d179328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d177461 q = 1) (hb : d180265 q = 1) : d180452 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d177461, d180265, d180452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d177461, d180265, d180452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d177462 q = 1) (hb : d180266 q = 1) : d180453 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d177462, d180266, d180453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177462, d180266, d180453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d177466 q = 1) (hb : d180268 q = 1) : d180455 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d177466, d180268, d180455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d177466, d180268, d180455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40750 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d144529 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d177467 q = 1) (hb : d180269 q = 1) : d180456 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d177467, d180269, d180456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d177467, d180269, d180456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d177468 q = 1) (hb : d180270 q = 1) : d180457 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d177468, d180270, d180457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d177468, d180270, d180457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d177469 q = 1) (hb : d180271 q = 1) : d180458 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d177469, d180271, d180458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d177469, d180271, d180458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d177470 q = 1) (hb : d180272 q = 1) : d180459 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d177470, d180272, d180459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d177470, d180272, d180459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d177508 q = 1) (hb : d180279 q = 1) : d180465 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d177508, d180279, d180465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d177508, d180279, d180465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40751 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d144590 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d177509 q = 1) (hb : d180280 q = 1) : d180466 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d177509, d180280, d180466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d177509, d180280, d180466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d177510 q = 1) (hb : d180281 q = 1) : d180467 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d177510, d180281, d180467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d177510, d180281, d180467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d177511 q = 1) (hb : d180282 q = 1) : d180468 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d177511, d180282, d180468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d177511, d180282, d180468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d177512 q = 1) (hb : d180283 q = 1) : d180469 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d177512, d180283, d180469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d177512, d180283, d180469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d177513 q = 1) (hb : d180284 q = 1) : d180470 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d177513, d180284, d180470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d177513, d180284, d180470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro40753 (p : Pattern) (ha : d177519 p = 1) (hb : d180290 p = 1) : d180476 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d177514 q = 1) (hb : d180285 q = 1) : d180471 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d177514, d180285, d180471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177514, d180285, d180471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40752 q ha hb
  have h2 (q : Pattern) (ha : d177515 q = 1) (hb : d180286 q = 1) : d180472 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d177515, d180286, d180472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177515, d180286, d180472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d177516 q = 1) (hb : d180287 q = 1) : d180473 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d177516, d180287, d180473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177516, d180287, d180473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d177517 q = 1) (hb : d180288 q = 1) : d180474 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d177517, d180288, d180474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177517, d180288, d180474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d177518 q = 1) (hb : d180289 q = 1) : d180475 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d177518, d180289, d180475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177518, d180289, d180475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d177519 q = 1) (hb : d180290 q = 1) : d180476 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d177519, d180290, d180476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177519, d180290, d180476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro40754 (p : Pattern) (ha : d177613 p = 1) (hb : d178469 p = 1) : d179513 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d177572 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d177581 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d177594 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d177546 q = 1) (hb : d178464 q = 1) : d179508 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d177546, d178464, d179508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40553 q ha hb
    | true =>
      simp only [d177546, d178464, d179508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40542 q hb ha
  have h5 (q : Pattern) (ha : d177595 q = 1) (hb : d178465 q = 1) : d179509 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d177595, d178465, d179509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d177595, d178465, d179509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d177609 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d177610 q = 1) (hb : d178466 q = 1) : d179510 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d177610, d178466, d179510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d177610, d178466, d179510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d177611 q = 1) (hb : d178467 q = 1) : d179511 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d177611, d178467, d179511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d177611, d178467, d179511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d177612 q = 1) (hb : d178468 q = 1) : d179512 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d177612, d178468, d179512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d177612, d178468, d179512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d177613 q = 1) (hb : d178469 q = 1) : d179513 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d177613, d178469, d179513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177613, d178469, d179513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro40755 (p : Pattern) (ha : d177634 p = 1) (hb : d178478 p = 1) : d179523 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d177572 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d177581 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d177594 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d177546 q = 1) (hb : d178464 q = 1) : d179508 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d177546, d178464, d179508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40553 q ha hb
    | true =>
      simp only [d177546, d178464, d179508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40542 q hb ha
  have h4 (q : Pattern) (ha : d177595 q = 1) (hb : d178465 q = 1) : d179509 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d177595, d178465, d179509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d177595, d178465, d179509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d177609 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d177610 q = 1) (hb : d178466 q = 1) : d179510 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d177610, d178466, d179510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d177610, d178466, d179510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d177611 q = 1) (hb : d178467 q = 1) : d179511 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d177611, d178467, d179511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d177611, d178467, d179511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d177612 q = 1) (hb : d178468 q = 1) : d179512 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d177612, d178468, d179512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177612, d178468, d179512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d177619 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d177624 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d177626 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d177556 q = 1) (hb : d178473 q = 1) : d179518 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d177556, d178473, d179518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40555 q ha hb
    | true =>
      simp only [d177556, d178473, d179518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40543 q hb ha
  have h13 (q : Pattern) (ha : d177627 q = 1) (hb : d178474 q = 1) : d179519 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d177627, d178474, d179519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d177627, d178474, d179519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d177630 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d177631 q = 1) (hb : d178475 q = 1) : d179520 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d177631, d178475, d179520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d177631, d178475, d179520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d177632 q = 1) (hb : d178476 q = 1) : d179521 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d177632, d178476, d179521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d177632, d178476, d179521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d177633 q = 1) (hb : d178477 q = 1) : d179522 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d177633, d178477, d179522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d177633, d178477, d179522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d177634 q = 1) (hb : d178478 q = 1) : d179523 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d177634, d178478, d179523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d177634, d178478, d179523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro40756 (p : Pattern) (ha : d177654 p = 1) (hb : d180295 p = 1) : d180481 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d177626 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d177556 q = 1) (hb : d178473 q = 1) : d179518 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d177556, d178473, d179518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40555 q ha hb
    | true =>
      simp only [d177556, d178473, d179518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40543 q hb ha
  have h3 (q : Pattern) (ha : d177627 q = 1) (hb : d178474 q = 1) : d179519 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d177627, d178474, d179519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d177627, d178474, d179519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d177630 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d177631 q = 1) (hb : d178475 q = 1) : d179520 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d177631, d178475, d179520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d177631, d178475, d179520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d177652 q = 1) (hb : d178476 q = 1) : d179521 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d177652, d178476, d179521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177652, d178476, d179521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d177653 q = 1) (hb : d178477 q = 1) : d179522 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d177653, d178477, d179522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177653, d178477, d179522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d177654 q = 1) (hb : d180295 q = 1) : d180481 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d177654, d180295, d180481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177654, d180295, d180481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro40757 (p : Pattern) (ha : d177718 p = 1) (hb : d180306 p = 1) : d180492 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d177694 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d177699 q = 1) (hb : d180301 q = 1) : d180487 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d177699, d180301, d180487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40584 q ha hb
    | true =>
      simp only [d177699, d180301, d180487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40548 q hb ha
  have h3 (q : Pattern) (ha : d177700 q = 1) (hb : d180302 q = 1) : d180488 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d177700, d180302, d180488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d177700, d180302, d180488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d177714 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d177715 q = 1) (hb : d180303 q = 1) : d180489 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d177715, d180303, d180489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d177715, d180303, d180489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d177716 q = 1) (hb : d180304 q = 1) : d180490 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d177716, d180304, d180490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177716, d180304, d180490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d177717 q = 1) (hb : d180305 q = 1) : d180491 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d177717, d180305, d180491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177717, d180305, d180491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d177718 q = 1) (hb : d180306 q = 1) : d180492 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d177718, d180306, d180492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177718, d180306, d180492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro40758 (p : Pattern) (ha : d177731 p = 1) (hb : d180312 p = 1) : d180498 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d177564 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d177635 q = 1) (hb : d178479 q = 1) : d179524 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d177635, d178479, d179524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40754 q ha hb
    | true =>
      simp only [d177635, d178479, d179524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40755 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d177648 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d177649 q = 1) (hb : d178480 q = 1) : d179525 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d177649, d178480, d179525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d177649, d178480, d179525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d177650 q = 1) (hb : d180293 q = 1) : d180479 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d177650, d180293, d180479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d177650, d180293, d180479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d177651 q = 1) (hb : d180294 q = 1) : d180480 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d177651, d180294, d180480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177651, d180294, d180480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d177655 q = 1) (hb : d180296 q = 1) : d180482 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d177655, d180296, d180482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d177655, d180296, d180482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40756 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d177657 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d177658 q = 1) (hb : d180297 q = 1) : d180483 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d177658, d180297, d180483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d177658, d180297, d180483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d177659 q = 1) (hb : d180298 q = 1) : d180484 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d177659, d180298, d180484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d177659, d180298, d180484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d177660 q = 1) (hb : d180299 q = 1) : d180485 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d177660, d180299, d180485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d177660, d180299, d180485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d177661 q = 1) (hb : d180300 q = 1) : d180486 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d177661, d180300, d180486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d177661, d180300, d180486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d177719 q = 1) (hb : d180307 q = 1) : d180493 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d177719, d180307, d180493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d177719, d180307, d180493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40757 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d177726 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d177727 q = 1) (hb : d180308 q = 1) : d180494 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d177727, d180308, d180494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d177727, d180308, d180494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d177728 q = 1) (hb : d180309 q = 1) : d180495 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d177728, d180309, d180495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d177728, d180309, d180495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d177729 q = 1) (hb : d180310 q = 1) : d180496 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d177729, d180310, d180496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d177729, d180310, d180496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d177730 q = 1) (hb : d180311 q = 1) : d180497 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d177730, d180311, d180497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d177730, d180311, d180497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d177731 q = 1) (hb : d180312 q = 1) : d180498 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d177731, d180312, d180498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d177731, d180312, d180498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro40759 (p : Pattern) (ha : d177737 p = 1) (hb : d180318 p = 1) : d180504 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d177732 q = 1) (hb : d180313 q = 1) : d180499 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d177732, d180313, d180499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177732, d180313, d180499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40758 q ha hb
  have h2 (q : Pattern) (ha : d177733 q = 1) (hb : d180314 q = 1) : d180500 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d177733, d180314, d180500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177733, d180314, d180500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d177734 q = 1) (hb : d180315 q = 1) : d180501 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d177734, d180315, d180501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177734, d180315, d180501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d177735 q = 1) (hb : d180316 q = 1) : d180502 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d177735, d180316, d180502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177735, d180316, d180502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d177736 q = 1) (hb : d180317 q = 1) : d180503 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d177736, d180317, d180503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177736, d180317, d180503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d177737 q = 1) (hb : d180318 q = 1) : d180504 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d177737, d180318, d180504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177737, d180318, d180504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro40760 (p : Pattern) (ha : d177832 p = 1) (hb : d178651 p = 1) : d179772 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d177791 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d177800 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d177813 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d177765 q = 1) (hb : d178646 q = 1) : d179767 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d177765, d178646, d179767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40597 q ha hb
    | true =>
      simp only [d177765, d178646, d179767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40598 q ha hb
  have h5 (q : Pattern) (ha : d177814 q = 1) (hb : d178647 q = 1) : d179768 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d177814, d178647, d179768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d177814, d178647, d179768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d177828 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d177829 q = 1) (hb : d178648 q = 1) : d179769 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d177829, d178648, d179769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d177829, d178648, d179769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d177830 q = 1) (hb : d178649 q = 1) : d179770 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d177830, d178649, d179770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d177830, d178649, d179770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d177831 q = 1) (hb : d178650 q = 1) : d179771 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d177831, d178650, d179771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d177831, d178650, d179771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d177832 q = 1) (hb : d178651 q = 1) : d179772 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d177832, d178651, d179772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177832, d178651, d179772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro40761 (p : Pattern) (ha : d177853 p = 1) (hb : d178661 p = 1) : d179782 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d177791 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d177800 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d177813 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d177765 q = 1) (hb : d178646 q = 1) : d179767 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d177765, d178646, d179767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40597 q ha hb
    | true =>
      simp only [d177765, d178646, d179767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40598 q ha hb
  have h4 (q : Pattern) (ha : d177814 q = 1) (hb : d178647 q = 1) : d179768 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d177814, d178647, d179768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d177814, d178647, d179768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d177828 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d177829 q = 1) (hb : d178648 q = 1) : d179769 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d177829, d178648, d179769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d177829, d178648, d179769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d177830 q = 1) (hb : d178649 q = 1) : d179770 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d177830, d178649, d179770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d177830, d178649, d179770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d177831 q = 1) (hb : d178650 q = 1) : d179771 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d177831, d178650, d179771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177831, d178650, d179771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d177838 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d177843 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d177845 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d177775 q = 1) (hb : d178656 q = 1) : d179777 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d177775, d178656, d179777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40600 q ha hb
    | true =>
      simp only [d177775, d178656, d179777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40601 q ha hb
  have h13 (q : Pattern) (ha : d177846 q = 1) (hb : d178657 q = 1) : d179778 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d177846, d178657, d179778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d177846, d178657, d179778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d177849 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d177850 q = 1) (hb : d178658 q = 1) : d179779 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d177850, d178658, d179779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d177850, d178658, d179779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d177851 q = 1) (hb : d178659 q = 1) : d179780 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d177851, d178659, d179780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d177851, d178659, d179780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d177852 q = 1) (hb : d178660 q = 1) : d179781 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d177852, d178660, d179781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d177852, d178660, d179781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d177853 q = 1) (hb : d178661 q = 1) : d179782 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d177853, d178661, d179782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d177853, d178661, d179782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro40762 (p : Pattern) (ha : d177873 p = 1) (hb : d180324 p = 1) : d180510 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d177845 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d177775 q = 1) (hb : d178656 q = 1) : d179777 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d177775, d178656, d179777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40600 q ha hb
    | true =>
      simp only [d177775, d178656, d179777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40601 q ha hb
  have h3 (q : Pattern) (ha : d177846 q = 1) (hb : d178657 q = 1) : d179778 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d177846, d178657, d179778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d177846, d178657, d179778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d177849 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d177850 q = 1) (hb : d178658 q = 1) : d179779 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d177850, d178658, d179779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d177850, d178658, d179779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d177871 q = 1) (hb : d178659 q = 1) : d179780 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d177871, d178659, d179780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177871, d178659, d179780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d177872 q = 1) (hb : d178660 q = 1) : d179781 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d177872, d178660, d179781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177872, d178660, d179781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d177873 q = 1) (hb : d180324 q = 1) : d180510 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d177873, d180324, d180510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177873, d180324, d180510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro40763 (p : Pattern) (ha : d177937 p = 1) (hb : d180335 p = 1) : d180521 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d177913 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d177918 q = 1) (hb : d180330 q = 1) : d180516 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d177918, d180330, d180516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40634 q ha hb
    | true =>
      simp only [d177918, d180330, d180516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40638 q ha hb
  have h3 (q : Pattern) (ha : d177919 q = 1) (hb : d180331 q = 1) : d180517 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d177919, d180331, d180517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d177919, d180331, d180517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d177933 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d177934 q = 1) (hb : d180332 q = 1) : d180518 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d177934, d180332, d180518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d177934, d180332, d180518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d177935 q = 1) (hb : d180333 q = 1) : d180519 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d177935, d180333, d180519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177935, d180333, d180519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d177936 q = 1) (hb : d180334 q = 1) : d180520 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d177936, d180334, d180520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177936, d180334, d180520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d177937 q = 1) (hb : d180335 q = 1) : d180521 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d177937, d180335, d180521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177937, d180335, d180521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro40764 (p : Pattern) (ha : d177950 p = 1) (hb : d180341 p = 1) : d180527 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d177783 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d177854 q = 1) (hb : d178662 q = 1) : d179783 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d177854, d178662, d179783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40760 q ha hb
    | true =>
      simp only [d177854, d178662, d179783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40761 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d177867 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d177868 q = 1) (hb : d178663 q = 1) : d179784 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d177868, d178663, d179784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d177868, d178663, d179784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d177869 q = 1) (hb : d180322 q = 1) : d180508 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d177869, d180322, d180508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d177869, d180322, d180508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d177870 q = 1) (hb : d180323 q = 1) : d180509 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d177870, d180323, d180509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177870, d180323, d180509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d177874 q = 1) (hb : d180325 q = 1) : d180511 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d177874, d180325, d180511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d177874, d180325, d180511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40762 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d177876 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d177877 q = 1) (hb : d180326 q = 1) : d180512 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d177877, d180326, d180512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d177877, d180326, d180512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d177878 q = 1) (hb : d180327 q = 1) : d180513 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d177878, d180327, d180513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d177878, d180327, d180513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d177879 q = 1) (hb : d180328 q = 1) : d180514 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d177879, d180328, d180514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d177879, d180328, d180514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d177880 q = 1) (hb : d180329 q = 1) : d180515 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d177880, d180329, d180515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d177880, d180329, d180515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d177938 q = 1) (hb : d180336 q = 1) : d180522 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d177938, d180336, d180522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d177938, d180336, d180522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40763 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d177945 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d177946 q = 1) (hb : d180337 q = 1) : d180523 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d177946, d180337, d180523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d177946, d180337, d180523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d177947 q = 1) (hb : d180338 q = 1) : d180524 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d177947, d180338, d180524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d177947, d180338, d180524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d177948 q = 1) (hb : d180339 q = 1) : d180525 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d177948, d180339, d180525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d177948, d180339, d180525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d177949 q = 1) (hb : d180340 q = 1) : d180526 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d177949, d180340, d180526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d177949, d180340, d180526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d177950 q = 1) (hb : d180341 q = 1) : d180527 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d177950, d180341, d180527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d177950, d180341, d180527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro40765 (p : Pattern) (ha : d177956 p = 1) (hb : d180347 p = 1) : d180533 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d177951 q = 1) (hb : d180342 q = 1) : d180528 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d177951, d180342, d180528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177951, d180342, d180528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40764 q ha hb
  have h2 (q : Pattern) (ha : d177952 q = 1) (hb : d180343 q = 1) : d180529 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d177952, d180343, d180529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177952, d180343, d180529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d177953 q = 1) (hb : d180344 q = 1) : d180530 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d177953, d180344, d180530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177953, d180344, d180530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d177954 q = 1) (hb : d180345 q = 1) : d180531 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d177954, d180345, d180531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177954, d180345, d180531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d177955 q = 1) (hb : d180346 q = 1) : d180532 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d177955, d180346, d180532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177955, d180346, d180532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d177956 q = 1) (hb : d180347 q = 1) : d180533 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d177956, d180347, d180533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177956, d180347, d180533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro40766 (p : Pattern) (ha : d178052 p = 1) (hb : d178876 p = 1) : d180029 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d178011 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d178020 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d178033 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d177985 q = 1) (hb : d178871 q = 1) : d180024 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d177985, d178871, d180024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40648 q ha hb
    | true =>
      simp only [d177985, d178871, d180024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40649 q ha hb
  have h5 (q : Pattern) (ha : d178034 q = 1) (hb : d178872 q = 1) : d180025 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d178034, d178872, d180025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d178034, d178872, d180025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d178048 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d178049 q = 1) (hb : d178873 q = 1) : d180026 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d178049, d178873, d180026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d178049, d178873, d180026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d178050 q = 1) (hb : d178874 q = 1) : d180027 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d178050, d178874, d180027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d178050, d178874, d180027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d178051 q = 1) (hb : d178875 q = 1) : d180028 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d178051, d178875, d180028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d178051, d178875, d180028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d178052 q = 1) (hb : d178876 q = 1) : d180029 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d178052, d178876, d180029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d178052, d178876, d180029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro40767 (p : Pattern) (ha : d178073 p = 1) (hb : d178886 p = 1) : d180039 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d178011 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d178020 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d178033 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d177985 q = 1) (hb : d178871 q = 1) : d180024 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d177985, d178871, d180024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40648 q ha hb
    | true =>
      simp only [d177985, d178871, d180024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40649 q ha hb
  have h4 (q : Pattern) (ha : d178034 q = 1) (hb : d178872 q = 1) : d180025 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d178034, d178872, d180025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d178034, d178872, d180025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d178048 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d178049 q = 1) (hb : d178873 q = 1) : d180026 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d178049, d178873, d180026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d178049, d178873, d180026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d178050 q = 1) (hb : d178874 q = 1) : d180027 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d178050, d178874, d180027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d178050, d178874, d180027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d178051 q = 1) (hb : d178875 q = 1) : d180028 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d178051, d178875, d180028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d178051, d178875, d180028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d178058 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d178063 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d178065 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d177995 q = 1) (hb : d178881 q = 1) : d180034 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d177995, d178881, d180034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40651 q ha hb
    | true =>
      simp only [d177995, d178881, d180034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40652 q ha hb
  have h13 (q : Pattern) (ha : d178066 q = 1) (hb : d178882 q = 1) : d180035 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d178066, d178882, d180035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d178066, d178882, d180035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d178069 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d178070 q = 1) (hb : d178883 q = 1) : d180036 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d178070, d178883, d180036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d178070, d178883, d180036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d178071 q = 1) (hb : d178884 q = 1) : d180037 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d178071, d178884, d180037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d178071, d178884, d180037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d178072 q = 1) (hb : d178885 q = 1) : d180038 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d178072, d178885, d180038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d178072, d178885, d180038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d178073 q = 1) (hb : d178886 q = 1) : d180039 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d178073, d178886, d180039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d178073, d178886, d180039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro40768 (p : Pattern) (ha : d178093 p = 1) (hb : d180354 p = 1) : d180540 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d178065 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d177995 q = 1) (hb : d178881 q = 1) : d180034 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d177995, d178881, d180034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40651 q ha hb
    | true =>
      simp only [d177995, d178881, d180034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40652 q ha hb
  have h3 (q : Pattern) (ha : d178066 q = 1) (hb : d178882 q = 1) : d180035 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d178066, d178882, d180035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d178066, d178882, d180035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d178069 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d178070 q = 1) (hb : d178883 q = 1) : d180036 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d178070, d178883, d180036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d178070, d178883, d180036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d178091 q = 1) (hb : d178884 q = 1) : d180037 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d178091, d178884, d180037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d178091, d178884, d180037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d178092 q = 1) (hb : d178885 q = 1) : d180038 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d178092, d178885, d180038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d178092, d178885, d180038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d178093 q = 1) (hb : d180354 q = 1) : d180540 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d178093, d180354, d180540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d178093, d180354, d180540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro40769 (p : Pattern) (ha : d178157 p = 1) (hb : d180365 p = 1) : d180551 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d178133 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d178138 q = 1) (hb : d180360 q = 1) : d180546 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d178138, d180360, d180546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40682 q ha hb
    | true =>
      simp only [d178138, d180360, d180546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40686 q ha hb
  have h3 (q : Pattern) (ha : d178139 q = 1) (hb : d180361 q = 1) : d180547 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d178139, d180361, d180547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d178139, d180361, d180547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d178153 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d178154 q = 1) (hb : d180362 q = 1) : d180548 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d178154, d180362, d180548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d178154, d180362, d180548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d178155 q = 1) (hb : d180363 q = 1) : d180549 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d178155, d180363, d180549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d178155, d180363, d180549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d178156 q = 1) (hb : d180364 q = 1) : d180550 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d178156, d180364, d180550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d178156, d180364, d180550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d178157 q = 1) (hb : d180365 q = 1) : d180551 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d178157, d180365, d180551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d178157, d180365, d180551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro40770 (p : Pattern) (ha : d178170 p = 1) (hb : d180371 p = 1) : d180557 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d178003 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d178074 q = 1) (hb : d178887 q = 1) : d180040 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d178074, d178887, d180040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40766 q ha hb
    | true =>
      simp only [d178074, d178887, d180040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40767 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d178087 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d178088 q = 1) (hb : d178888 q = 1) : d180041 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d178088, d178888, d180041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d178088, d178888, d180041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d178089 q = 1) (hb : d180352 q = 1) : d180538 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d178089, d180352, d180538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d178089, d180352, d180538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d178090 q = 1) (hb : d180353 q = 1) : d180539 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d178090, d180353, d180539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d178090, d180353, d180539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d178094 q = 1) (hb : d180355 q = 1) : d180541 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d178094, d180355, d180541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d178094, d180355, d180541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40768 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d178096 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d178097 q = 1) (hb : d180356 q = 1) : d180542 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d178097, d180356, d180542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d178097, d180356, d180542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d178098 q = 1) (hb : d180357 q = 1) : d180543 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d178098, d180357, d180543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d178098, d180357, d180543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d178099 q = 1) (hb : d180358 q = 1) : d180544 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d178099, d180358, d180544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d178099, d180358, d180544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d178100 q = 1) (hb : d180359 q = 1) : d180545 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d178100, d180359, d180545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d178100, d180359, d180545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d178158 q = 1) (hb : d180366 q = 1) : d180552 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d178158, d180366, d180552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d178158, d180366, d180552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40769 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d178165 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d178166 q = 1) (hb : d180367 q = 1) : d180553 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d178166, d180367, d180553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d178166, d180367, d180553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d178167 q = 1) (hb : d180368 q = 1) : d180554 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d178167, d180368, d180554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d178167, d180368, d180554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d178168 q = 1) (hb : d180369 q = 1) : d180555 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d178168, d180369, d180555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d178168, d180369, d180555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d178169 q = 1) (hb : d180370 q = 1) : d180556 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d178169, d180370, d180556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d178169, d180370, d180556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d178170 q = 1) (hb : d180371 q = 1) : d180557 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d178170, d180371, d180557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d178170, d180371, d180557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro40771 (p : Pattern) (ha : d178176 p = 1) (hb : d180377 p = 1) : d180563 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d178171 q = 1) (hb : d180372 q = 1) : d180558 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d178171, d180372, d180558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d178171, d180372, d180558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40770 q ha hb
  have h2 (q : Pattern) (ha : d178172 q = 1) (hb : d180373 q = 1) : d180559 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d178172, d180373, d180559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d178172, d180373, d180559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d178173 q = 1) (hb : d180374 q = 1) : d180560 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d178173, d180374, d180560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d178173, d180374, d180560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d178174 q = 1) (hb : d180375 q = 1) : d180561 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d178174, d180375, d180561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d178174, d180375, d180561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d178175 q = 1) (hb : d180376 q = 1) : d180562 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d178175, d180376, d180562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d178175, d180376, d180562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d178176 q = 1) (hb : d180377 q = 1) : d180563 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d178176, d180377, d180563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d178176, d180377, d180563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro40772 (p : Pattern) (ha : d178182 p = 1) (hb : d180383 p = 1) : d180569 p = 1 := by
  have h0 (q : Pattern) (ha : d161075 q = 1) (hb : d177371 q = 1) : d180451 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d161075, d177371, d180451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40741 q ha hb
    | true =>
      simp only [d161075, d177371, d180451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40747 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d177520 q = 1) (hb : d180291 q = 1) : d180477 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d177520, d180291, d180477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d177520, d180291, d180477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40753 q ha hb
  have h3 (q : Pattern) (ha : d177521 q = 1) (hb : d180292 q = 1) : d180478 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d177521, d180292, d180478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177521, d180292, d180478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d177738 q = 1) (hb : d180319 q = 1) : d180505 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d177738, d180319, d180505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d177738, d180319, d180505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40759 q ha hb
  have h5 (q : Pattern) (ha : d177739 q = 1) (hb : d180320 q = 1) : d180506 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d177739, d180320, d180506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d177739, d180320, d180506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d177740 q = 1) (hb : d180321 q = 1) : d180507 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d177740, d180321, d180507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d177740, d180321, d180507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d177957 q = 1) (hb : d180348 q = 1) : d180534 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d177957, d180348, d180534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d177957, d180348, d180534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40765 q ha hb
  have h8 (q : Pattern) (ha : d177958 q = 1) (hb : d180349 q = 1) : d180535 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d177958, d180349, d180535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d177958, d180349, d180535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d177959 q = 1) (hb : d180350 q = 1) : d180536 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d177959, d180350, d180536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d177959, d180350, d180536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d177960 q = 1) (hb : d180351 q = 1) : d180537 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d177960, d180351, d180537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d177960, d180351, d180537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d178177 q = 1) (hb : d180378 q = 1) : d180564 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d178177, d180378, d180564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d178177, d180378, d180564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40771 q ha hb
  have h12 (q : Pattern) (ha : d178178 q = 1) (hb : d180379 q = 1) : d180565 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d178178, d180379, d180565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d178178, d180379, d180565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d178179 q = 1) (hb : d180380 q = 1) : d180566 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d178179, d180380, d180566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d178179, d180380, d180566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d178180 q = 1) (hb : d180381 q = 1) : d180567 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d178180, d180381, d180567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d178180, d180381, d180567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d178181 q = 1) (hb : d180382 q = 1) : d180568 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d178181, d180382, d180568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d178181, d180382, d180568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d178182 q = 1) (hb : d180383 q = 1) : d180569 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d178182, d180383, d180569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d178182, d180383, d180569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro40773 (p : Pattern) (ha : d178188 p = 1) (hb : d180389 p = 1) : d180575 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d178183 q = 1) (hb : d180384 q = 1) : d180570 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d178183, d180384, d180570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40772 q ha hb
    | true =>
      simp only [d178183, d180384, d180570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d178184 q = 1) (hb : d180385 q = 1) : d180571 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d178184, d180385, d180571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d178184, d180385, d180571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d178185 q = 1) (hb : d180386 q = 1) : d180572 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d178185, d180386, d180572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d178185, d180386, d180572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d178186 q = 1) (hb : d180387 q = 1) : d180573 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d178186, d180387, d180573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d178186, d180387, d180573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d178187 q = 1) (hb : d180388 q = 1) : d180574 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d178187, d180388, d180574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d178187, d180388, d180574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d178188 q = 1) (hb : d180389 q = 1) : d180575 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d178188, d180389, d180575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d178188, d180389, d180575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro40774 (p : Pattern) (ha : d178194 p = 1) (hb : d180395 p = 1) : d180581 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d178189 q = 1) (hb : d180390 q = 1) : d180576 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d178189, d180390, d180576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40773 q ha hb
    | true =>
      simp only [d178189, d180390, d180576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d178190 q = 1) (hb : d180391 q = 1) : d180577 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d178190, d180391, d180577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d178190, d180391, d180577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d178191 q = 1) (hb : d180392 q = 1) : d180578 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d178191, d180392, d180578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d178191, d180392, d180578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d178192 q = 1) (hb : d180393 q = 1) : d180579 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d178192, d180393, d180579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d178192, d180393, d180579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d178193 q = 1) (hb : d180394 q = 1) : d180580 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d178193, d180394, d180580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d178193, d180394, d180580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d178194 q = 1) (hb : d180395 q = 1) : d180581 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d178194, d180395, d180581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d178194, d180395, d180581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro40775 (p : Pattern) (ha : d178200 p = 1) (hb : d180401 p = 1) : d180587 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d178195 q = 1) (hb : d180396 q = 1) : d180582 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d178195, d180396, d180582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40774 q ha hb
    | true =>
      simp only [d178195, d180396, d180582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d178196 q = 1) (hb : d180397 q = 1) : d180583 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d178196, d180397, d180583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d178196, d180397, d180583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d178197 q = 1) (hb : d180398 q = 1) : d180584 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d178197, d180398, d180584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d178197, d180398, d180584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d178198 q = 1) (hb : d180399 q = 1) : d180585 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d178198, d180399, d180585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d178198, d180399, d180585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d178199 q = 1) (hb : d180400 q = 1) : d180586 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d178199, d180400, d180586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d178199, d180400, d180586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d178200 q = 1) (hb : d180401 q = 1) : d180587 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d178200, d180401, d180587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d178200, d180401, d180587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro40776 (p : Pattern) (ha : d178206 p = 1) (hb : d180407 p = 1) : d180593 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d178201 q = 1) (hb : d180402 q = 1) : d180588 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d178201, d180402, d180588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40775 q ha hb
    | true =>
      simp only [d178201, d180402, d180588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d178202 q = 1) (hb : d180403 q = 1) : d180589 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d178202, d180403, d180589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d178202, d180403, d180589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d178203 q = 1) (hb : d180404 q = 1) : d180590 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d178203, d180404, d180590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d178203, d180404, d180590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d178204 q = 1) (hb : d180405 q = 1) : d180591 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d178204, d180405, d180591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d178204, d180405, d180591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d178205 q = 1) (hb : d180406 q = 1) : d180592 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d178205, d180406, d180592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d178205, d180406, d180592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d178206 q = 1) (hb : d180407 q = 1) : d180593 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d178206, d180407, d180593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d178206, d180407, d180593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro40777 (p : Pattern) (ha : d178212 p = 1) (hb : d180413 p = 1) : d180599 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d178207 q = 1) (hb : d180408 q = 1) : d180594 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d178207, d180408, d180594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40776 q ha hb
    | true =>
      simp only [d178207, d180408, d180594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d178208 q = 1) (hb : d180409 q = 1) : d180595 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d178208, d180409, d180595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d178208, d180409, d180595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d178209 q = 1) (hb : d180410 q = 1) : d180596 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d178209, d180410, d180596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d178209, d180410, d180596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d178210 q = 1) (hb : d180411 q = 1) : d180597 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d178210, d180411, d180597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d178210, d180411, d180597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d178211 q = 1) (hb : d180412 q = 1) : d180598 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d178211, d180412, d180598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d178211, d180412, d180598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d178212 q = 1) (hb : d180413 q = 1) : d180599 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d178212, d180413, d180599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d178212, d180413, d180599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro40778 (p : Pattern) (ha : d178218 p = 1) (hb : d180419 p = 1) : d180605 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d178213 q = 1) (hb : d180414 q = 1) : d180600 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d178213, d180414, d180600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40777 q ha hb
    | true =>
      simp only [d178213, d180414, d180600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d178214 q = 1) (hb : d180415 q = 1) : d180601 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d178214, d180415, d180601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d178214, d180415, d180601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d178215 q = 1) (hb : d180416 q = 1) : d180602 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d178215, d180416, d180602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d178215, d180416, d180602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d178216 q = 1) (hb : d180417 q = 1) : d180603 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d178216, d180417, d180603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d178216, d180417, d180603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d178217 q = 1) (hb : d180418 q = 1) : d180604 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d178217, d180418, d180604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d178217, d180418, d180604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d178218 q = 1) (hb : d180419 q = 1) : d180605 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d178218, d180419, d180605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d178218, d180419, d180605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro40779 (p : Pattern) (ha : d178224 p = 1) (hb : d180425 p = 1) : d180611 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d178219 q = 1) (hb : d180420 q = 1) : d180606 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d178219, d180420, d180606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40778 q ha hb
    | true =>
      simp only [d178219, d180420, d180606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d178220 q = 1) (hb : d180421 q = 1) : d180607 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d178220, d180421, d180607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d178220, d180421, d180607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d178221 q = 1) (hb : d180422 q = 1) : d180608 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d178221, d180422, d180608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d178221, d180422, d180608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d178222 q = 1) (hb : d180423 q = 1) : d180609 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d178222, d180423, d180609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d178222, d180423, d180609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d178223 q = 1) (hb : d180424 q = 1) : d180610 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d178223, d180424, d180610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d178223, d180424, d180610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d178224 q = 1) (hb : d180425 q = 1) : d180611 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d178224, d180425, d180611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d178224, d180425, d180611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro40780 (p : Pattern) (ha : d159868 p = 1) (hb : d180616 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d142751 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d142757 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d175944 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d159810 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d159864 q = 1) (hb : d180612 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d159864, d180612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d159864, d180612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d142680 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d159865 q = 1) (hb : d180613 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d159865, d180613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d159865, d180613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d159866 q = 1) (hb : d180614 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d159866, d180614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d159866, d180614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d159867 q = 1) (hb : d180615 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d159867, d180615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d159867, d180615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d159868 q = 1) (hb : d180616 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d159868, d180616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d159868, d180616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro40781 (p : Pattern) (ha : d159875 p = 1) (hb : d180621 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142751 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d142757 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d175944 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d159810 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d159864 q = 1) (hb : d180612 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d159864, d180612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d159864, d180612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d142680 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d159865 q = 1) (hb : d180613 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d159865, d180613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d159865, d180613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d159866 q = 1) (hb : d180614 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d159866, d180614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d159866, d180614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d159867 q = 1) (hb : d180615 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d159867, d180615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d159867, d180615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d142793 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d142797 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d175951 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d159817 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d159871 q = 1) (hb : d180617 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d159871, d180617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d159871, d180617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d142687 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d159872 q = 1) (hb : d180618 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d159872, d180618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d159872, d180618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d159873 q = 1) (hb : d180619 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d159873, d180619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d159873, d180619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d159874 q = 1) (hb : d180620 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d159874, d180620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d159874, d180620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d159875 q = 1) (hb : d180621 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d159875, d180621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d159875, d180621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro40782 (p : Pattern) (ha : d160055 p = 1) (hb : d180628 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d175951 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d159817 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d159871 q = 1) (hb : d180617 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d159871, d180617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d159871, d180617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d142687 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d159872 q = 1) (hb : d180618 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d159872, d180618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d159872, d180618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d159873 q = 1) (hb : d180626 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d159873, d180626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d159873, d180626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d159874 q = 1) (hb : d180627 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d159874, d180627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d159874, d180627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d160055 q = 1) (hb : d180628 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d160055, d180628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d160055, d180628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro40783 (p : Pattern) (ha : d160092 p = 1) (hb : d180638 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d175981 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d159847 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d160088 q = 1) (hb : d180634 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d160088, d180634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d160088, d180634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d142715 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d160089 q = 1) (hb : d180635 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d160089, d180635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d160089, d180635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d160090 q = 1) (hb : d180636 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d160090, d180636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d160090, d180636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d160091 q = 1) (hb : d180637 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d160091, d180637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d160091, d180637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d160092 q = 1) (hb : d180638 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d160092, d180638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d160092, d180638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro40784 (p : Pattern) (ha : d161043 p = 1) (hb : d180644 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142745 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d159876 q = 1) (hb : d180622 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d159876, d180622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40780 q ha hb
    | true =>
      simp only [d159876, d180622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40781 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d142809 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d159877 q = 1) (hb : d180623 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d159877, d180623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d159877, d180623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d161033 q = 1) (hb : d180624 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d161033, d180624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d161033, d180624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d161034 q = 1) (hb : d180625 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d161034, d180625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d161034, d180625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d160056 q = 1) (hb : d180629 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d160056, d180629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d160056, d180629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40782 q ha hb
  have h8 (q : Pattern) (ha : d161035 q = 1) (hb : d180630 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d161035, d180630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d161035, d180630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h9 (q : Pattern) (ha : d161036 q = 1) (hb : d180631 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d161036, d180631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d161036, d180631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d161037 q = 1) (hb : d180632 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d161037, d180632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d161037, d180632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d161038 q = 1) (hb : d180633 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d161038, d180633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d161038, d180633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d160093 q = 1) (hb : d180639 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d160093, d180639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d160093, d180639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40783 q ha hb
  have h13 (q : Pattern) (ha : d161039 q = 1) (hb : d180640 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d161039, d180640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d161039, d180640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h14 (q : Pattern) (ha : d161040 q = 1) (hb : d180641 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d161040, d180641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d161040, d180641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h15 (q : Pattern) (ha : d161041 q = 1) (hb : d180642 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d161041, d180642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d161041, d180642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h16 (q : Pattern) (ha : d161042 q = 1) (hb : d180643 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d161042, d180643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d161042, d180643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d161043 q = 1) (hb : d180644 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d161043, d180644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d161043, d180644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro40785 (p : Pattern) (ha : d161049 p = 1) (hb : d180650 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142730 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d161044 q = 1) (hb : d180645 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d161044, d180645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d161044, d180645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40784 q ha hb
  have h3 (q : Pattern) (ha : d161045 q = 1) (hb : d180646 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d161045, d180646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d161045, d180646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d161046 q = 1) (hb : d180647 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d161046, d180647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d161046, d180647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d161047 q = 1) (hb : d180648 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d161047, d180648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d161047, d180648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d161048 q = 1) (hb : d180649 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d161048, d180649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d161048, d180649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d161049 q = 1) (hb : d180650 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d161049, d180650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d161049, d180650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro40786 (p : Pattern) (ha : d159977 p = 1) (hb : d180655 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d176019 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d176025 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d176038 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d159905 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d159973 q = 1) (hb : d180651 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d159973, d180651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d159973, d180651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d176058 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d159974 q = 1) (hb : d180652 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d159974, d180652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d159974, d180652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d159975 q = 1) (hb : d180653 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d159975, d180653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d159975, d180653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d159976 q = 1) (hb : d180654 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d159976, d180654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d159976, d180654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d159977 q = 1) (hb : d180655 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d159977, d180655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d159977, d180655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro40787 (p : Pattern) (ha : d159984 p = 1) (hb : d180660 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d176019 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d176025 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d176038 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d159905 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d159973 q = 1) (hb : d180651 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d159973, d180651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d159973, d180651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d176058 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d159974 q = 1) (hb : d180652 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d159974, d180652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d159974, d180652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d159975 q = 1) (hb : d180653 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d159975, d180653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d159975, d180653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d159976 q = 1) (hb : d180654 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d159976, d180654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d159976, d180654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d176067 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d176071 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d176073 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d159921 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d159980 q = 1) (hb : d180656 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d159980, d180656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d159980, d180656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d176079 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d159981 q = 1) (hb : d180657 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d159981, d180657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d159981, d180657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d159982 q = 1) (hb : d180658 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d159982, d180658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d159982, d180658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d159983 q = 1) (hb : d180659 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d159983, d180659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d159983, d180659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d159984 q = 1) (hb : d180660 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d159984, d180660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d159984, d180660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro40788 (p : Pattern) (ha : d161052 p = 1) (hb : d180667 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d176073 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d159921 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d159980 q = 1) (hb : d180656 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d159980, d180656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d159980, d180656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d176079 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d159981 q = 1) (hb : d180657 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d159981, d180657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d159981, d180657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d159982 q = 1) (hb : d180665 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d159982, d180665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d159982, d180665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d159983 q = 1) (hb : d180666 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d159983, d180666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d159983, d180666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d161052 q = 1) (hb : d180667 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d161052, d180667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d161052, d180667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro40789 (p : Pattern) (ha : d161062 p = 1) (hb : d180677 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d176110 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d159955 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d161058 q = 1) (hb : d180673 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d161058, d180673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d161058, d180673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d176130 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d161059 q = 1) (hb : d180674 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d161059, d180674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d161059, d180674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d161060 q = 1) (hb : d180675 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d161060, d180675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d161060, d180675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d161061 q = 1) (hb : d180676 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d161061, d180676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d161061, d180676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d161062 q = 1) (hb : d180677 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d161062, d180677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d161062, d180677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro40790 (p : Pattern) (ha : d161068 p = 1) (hb : d180683 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d176013 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d159985 q = 1) (hb : d180661 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d159985, d180661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40786 q ha hb
    | true =>
      simp only [d159985, d180661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40787 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d176086 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d159986 q = 1) (hb : d180662 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d159986, d180662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d159986, d180662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d161050 q = 1) (hb : d180663 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d161050, d180663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d161050, d180663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d161051 q = 1) (hb : d180664 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d161051, d180664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d161051, d180664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d161053 q = 1) (hb : d180668 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d161053, d180668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d161053, d180668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40788 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d142960 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d161054 q = 1) (hb : d180669 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d161054, d180669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d161054, d180669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d161055 q = 1) (hb : d180670 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d161055, d180670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d161055, d180670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d161056 q = 1) (hb : d180671 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d161056, d180671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d161056, d180671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d161057 q = 1) (hb : d180672 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d161057, d180672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d161057, d180672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d161063 q = 1) (hb : d180678 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d161063, d180678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d161063, d180678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40789 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d143008 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d161064 q = 1) (hb : d180679 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d161064, d180679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d161064, d180679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d161065 q = 1) (hb : d180680 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d161065, d180680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d161065, d180680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d161066 q = 1) (hb : d180681 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d161066, d180681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d161066, d180681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d161067 q = 1) (hb : d180682 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d161067, d180682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d161067, d180682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d161068 q = 1) (hb : d180683 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d161068, d180683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d161068, d180683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro40791 (p : Pattern) (ha : d161074 p = 1) (hb : d180689 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d161069 q = 1) (hb : d180684 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d161069, d180684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d161069, d180684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40790 q ha hb
  have h2 (q : Pattern) (ha : d161070 q = 1) (hb : d180685 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d161070, d180685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d161070, d180685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d161071 q = 1) (hb : d180686 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d161071, d180686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d161071, d180686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d161072 q = 1) (hb : d180687 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d161072, d180687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d161072, d180687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d161073 q = 1) (hb : d180688 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d161073, d180688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d161073, d180688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d161074 q = 1) (hb : d180689 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d161074, d180689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d161074, d180689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro40792 (p : Pattern) (ha : d178314 p = 1) (hb : d180695 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d176183 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d176189 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d176202 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d178309 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d178310 q = 1) (hb : d180691 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d178310, d180691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d178310, d180691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d176222 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d178311 q = 1) (hb : d180692 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d178311, d180692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d178311, d180692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d178312 q = 1) (hb : d180693 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d178312, d180693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d178312, d180693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d178313 q = 1) (hb : d180694 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d178313, d180694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d178313, d180694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d178314 q = 1) (hb : d180695 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d178314, d180695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d178314, d180695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro40793 (p : Pattern) (ha : d178323 p = 1) (hb : d180700 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d176183 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d176189 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d176202 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d178309 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d178310 q = 1) (hb : d180691 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d178310, d180691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d178310, d180691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d176222 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d178311 q = 1) (hb : d180692 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d178311, d180692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d178311, d180692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d178312 q = 1) (hb : d180693 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d178312, d180693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d178312, d180693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d178313 q = 1) (hb : d180694 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d178313, d180694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d178313, d180694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d176231 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d176235 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d176237 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d178318 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d178319 q = 1) (hb : d180696 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d178319, d180696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d178319, d180696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d176243 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d178320 q = 1) (hb : d180697 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d178320, d180697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d178320, d180697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d178321 q = 1) (hb : d180698 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d178321, d180698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d178321, d180698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d178322 q = 1) (hb : d180699 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d178322, d180699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d178322, d180699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d178323 q = 1) (hb : d180700 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d178323, d180700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d178323, d180700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro40794 (p : Pattern) (ha : d180267 p = 1) (hb : d180707 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d176237 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d178318 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d178319 q = 1) (hb : d180696 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d178319, d180696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d178319, d180696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d176243 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d178320 q = 1) (hb : d180697 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d178320, d180697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d178320, d180697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d178321 q = 1) (hb : d180705 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d178321, d180705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d178321, d180705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d178322 q = 1) (hb : d180706 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d178322, d180706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d178322, d180706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d180267 q = 1) (hb : d180707 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d180267, d180707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d180267, d180707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro40795 (p : Pattern) (ha : d180278 p = 1) (hb : d180717 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d176286 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d180273 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d180274 q = 1) (hb : d180713 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d180274, d180713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d180274, d180713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d176306 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d180275 q = 1) (hb : d180714 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d180275, d180714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d180275, d180714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d180276 q = 1) (hb : d180715 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d180276, d180715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d180276, d180715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d180277 q = 1) (hb : d180716 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d180277, d180716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d180277, d180716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d180278 q = 1) (hb : d180717 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d180278, d180717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d180278, d180717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro40796 (p : Pattern) (ha : d180284 p = 1) (hb : d180723 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d176177 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d178324 q = 1) (hb : d180701 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d178324, d180701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40792 q ha hb
    | true =>
      simp only [d178324, d180701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40793 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d176250 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d178325 q = 1) (hb : d180702 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d178325, d180702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d178325, d180702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d180265 q = 1) (hb : d180703 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d180265, d180703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d180265, d180703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d180266 q = 1) (hb : d180704 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d180266, d180704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d180266, d180704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d180268 q = 1) (hb : d180708 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d180268, d180708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d180268, d180708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40794 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d143176 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d180269 q = 1) (hb : d180709 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d180269, d180709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d180269, d180709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d180270 q = 1) (hb : d180710 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d180270, d180710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d180270, d180710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d180271 q = 1) (hb : d180711 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d180271, d180711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d180271, d180711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d180272 q = 1) (hb : d180712 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d180272, d180712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d180272, d180712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d180279 q = 1) (hb : d180718 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d180279, d180718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d180279, d180718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40795 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d143261 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d180280 q = 1) (hb : d180719 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d180280, d180719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d180280, d180719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d180281 q = 1) (hb : d180720 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d180281, d180720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d180281, d180720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d180282 q = 1) (hb : d180721 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d180282, d180721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d180282, d180721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d180283 q = 1) (hb : d180722 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d180283, d180722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d180283, d180722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d180284 q = 1) (hb : d180723 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d180284, d180723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d180284, d180723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro40797 (p : Pattern) (ha : d180290 p = 1) (hb : d180729 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d180285 q = 1) (hb : d180724 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d180285, d180724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d180285, d180724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40796 q ha hb
  have h2 (q : Pattern) (ha : d180286 q = 1) (hb : d180725 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d180286, d180725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d180286, d180725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d180287 q = 1) (hb : d180726 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d180287, d180726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d180287, d180726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d180288 q = 1) (hb : d180727 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d180288, d180727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d180288, d180727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d180289 q = 1) (hb : d180728 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d180289, d180728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d180289, d180728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d180290 q = 1) (hb : d180729 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d180290, d180729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d180290, d180729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro40798 (p : Pattern) (ha : d178469 p = 1) (hb : d180736 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d176375 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d176384 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d176397 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d178464 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d178465 q = 1) (hb : d180732 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d178465, d180732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d178465, d180732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d176437 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d178466 q = 1) (hb : d180733 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d178466, d180733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d178466, d180733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d178467 q = 1) (hb : d180734 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d178467, d180734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d178467, d180734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d178468 q = 1) (hb : d180735 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d178468, d180735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d178468, d180735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d178469 q = 1) (hb : d180736 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d178469, d180736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d178469, d180736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro40799 (p : Pattern) (ha : d178478 p = 1) (hb : d180741 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d176375 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d176384 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d176397 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d178464 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d178465 q = 1) (hb : d180732 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d178465, d180732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d178465, d180732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d176437 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d178466 q = 1) (hb : d180733 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d178466, d180733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d178466, d180733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d178467 q = 1) (hb : d180734 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d178467, d180734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d178467, d180734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d178468 q = 1) (hb : d180735 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d178468, d180735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d178468, d180735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d176447 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d176452 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d176454 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d178473 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d178474 q = 1) (hb : d180737 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d178474, d180737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d178474, d180737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d176461 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d178475 q = 1) (hb : d180738 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d178475, d180738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d178475, d180738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d178476 q = 1) (hb : d180739 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d178476, d180739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d178476, d180739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d178477 q = 1) (hb : d180740 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d178477, d180740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d178477, d180740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d178478 q = 1) (hb : d180741 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d178478, d180741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d178478, d180741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro40800 (p : Pattern) (ha : d180295 p = 1) (hb : d180748 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d176454 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d178473 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d178474 q = 1) (hb : d180737 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d178474, d180737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d178474, d180737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d176461 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d178475 q = 1) (hb : d180738 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d178475, d180738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d178475, d180738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d178476 q = 1) (hb : d180746 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d178476, d180746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d178476, d180746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d178477 q = 1) (hb : d180747 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d178477, d180747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d178477, d180747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d180295 q = 1) (hb : d180748 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d180295, d180748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d180295, d180748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro40801 (p : Pattern) (ha : d180306 p = 1) (hb : d180758 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d176525 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d180301 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d180302 q = 1) (hb : d180754 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d180302, d180754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d180302, d180754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d176565 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d180303 q = 1) (hb : d180755 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d180303, d180755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d180303, d180755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d180304 q = 1) (hb : d180756 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d180304, d180756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d180304, d180756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d180305 q = 1) (hb : d180757 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d180305, d180757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d180305, d180757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d180306 q = 1) (hb : d180758 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d180306, d180758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d180306, d180758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro40802 (p : Pattern) (ha : d180312 p = 1) (hb : d180764 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d176367 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d178479 q = 1) (hb : d180742 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d178479, d180742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40798 q ha hb
    | true =>
      simp only [d178479, d180742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40799 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d176479 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d178480 q = 1) (hb : d180743 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d178480, d180743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d178480, d180743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d180293 q = 1) (hb : d180744 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d180293, d180744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d180293, d180744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d180294 q = 1) (hb : d180745 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d180294, d180745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d180294, d180745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d180296 q = 1) (hb : d180749 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d180296, d180749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d180296, d180749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40800 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d176488 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d180297 q = 1) (hb : d180750 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d180297, d180750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d180297, d180750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d180298 q = 1) (hb : d180751 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d180298, d180751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d180298, d180751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d180299 q = 1) (hb : d180752 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d180299, d180752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d180299, d180752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d180300 q = 1) (hb : d180753 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d180300, d180753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d180300, d180753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d180307 q = 1) (hb : d180759 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d180307, d180759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d180307, d180759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40801 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d176581 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d180308 q = 1) (hb : d180760 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d180308, d180760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d180308, d180760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d180309 q = 1) (hb : d180761 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d180309, d180761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d180309, d180761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d180310 q = 1) (hb : d180762 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d180310, d180762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d180310, d180762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d180311 q = 1) (hb : d180763 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d180311, d180763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d180311, d180763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d180312 q = 1) (hb : d180764 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d180312, d180764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d180312, d180764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro40803 (p : Pattern) (ha : d180318 p = 1) (hb : d180770 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d180313 q = 1) (hb : d180765 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d180313, d180765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d180313, d180765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40802 q ha hb
  have h2 (q : Pattern) (ha : d180314 q = 1) (hb : d180766 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d180314, d180766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d180314, d180766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d180315 q = 1) (hb : d180767 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d180315, d180767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d180315, d180767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d180316 q = 1) (hb : d180768 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d180316, d180768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d180316, d180768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d180317 q = 1) (hb : d180769 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d180317, d180769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d180317, d180769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d180318 q = 1) (hb : d180770 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d180318, d180770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d180318, d180770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro40804 (p : Pattern) (ha : d178651 p = 1) (hb : d180778 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d176646 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d176655 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d176668 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d178646 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d178647 q = 1) (hb : d180774 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d178647, d180774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d178647, d180774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d176708 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d178648 q = 1) (hb : d180775 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d178648, d180775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d178648, d180775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d178649 q = 1) (hb : d180776 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d178649, d180776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d178649, d180776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d178650 q = 1) (hb : d180777 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d178650, d180777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d178650, d180777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d178651 q = 1) (hb : d180778 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d178651, d180778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d178651, d180778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro40805 (p : Pattern) (ha : d178661 p = 1) (hb : d180783 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d176646 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d176655 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d176668 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d178646 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d178647 q = 1) (hb : d180774 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d178647, d180774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d178647, d180774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d176708 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d178648 q = 1) (hb : d180775 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d178648, d180775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d178648, d180775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d178649 q = 1) (hb : d180776 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d178649, d180776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d178649, d180776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d178650 q = 1) (hb : d180777 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d178650, d180777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d178650, d180777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d176718 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d176723 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d176725 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d178656 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d178657 q = 1) (hb : d180779 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d178657, d180779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d178657, d180779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d176732 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d178658 q = 1) (hb : d180780 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d178658, d180780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d178658, d180780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d178659 q = 1) (hb : d180781 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d178659, d180781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d178659, d180781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d178660 q = 1) (hb : d180782 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d178660, d180782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d178660, d180782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d178661 q = 1) (hb : d180783 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d178661, d180783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d178661, d180783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro40806 (p : Pattern) (ha : d180324 p = 1) (hb : d180790 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d176725 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d178656 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d178657 q = 1) (hb : d180779 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d178657, d180779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d178657, d180779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d176732 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d178658 q = 1) (hb : d180780 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d178658, d180780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d178658, d180780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d178659 q = 1) (hb : d180788 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d178659, d180788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d178659, d180788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d178660 q = 1) (hb : d180789 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d178660, d180789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d178660, d180789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d180324 q = 1) (hb : d180790 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d180324, d180790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d180324, d180790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro40807 (p : Pattern) (ha : d180335 p = 1) (hb : d180800 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d176796 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d180330 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d180331 q = 1) (hb : d180796 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d180331, d180796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d180331, d180796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d176836 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d180332 q = 1) (hb : d180797 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d180332, d180797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d180332, d180797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d180333 q = 1) (hb : d180798 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d180333, d180798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d180333, d180798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d180334 q = 1) (hb : d180799 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d180334, d180799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d180334, d180799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d180335 q = 1) (hb : d180800 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d180335, d180800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d180335, d180800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro40808 (p : Pattern) (ha : d180341 p = 1) (hb : d180806 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d176638 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d178662 q = 1) (hb : d180784 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d178662, d180784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40804 q ha hb
    | true =>
      simp only [d178662, d180784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40805 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d176750 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d178663 q = 1) (hb : d180785 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d178663, d180785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d178663, d180785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d180322 q = 1) (hb : d180786 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d180322, d180786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d180322, d180786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d180323 q = 1) (hb : d180787 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d180323, d180787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d180323, d180787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d180325 q = 1) (hb : d180791 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d180325, d180791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d180325, d180791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40806 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d176759 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d180326 q = 1) (hb : d180792 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d180326, d180792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d180326, d180792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d180327 q = 1) (hb : d180793 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d180327, d180793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d180327, d180793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d180328 q = 1) (hb : d180794 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d180328, d180794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d180328, d180794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d180329 q = 1) (hb : d180795 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d180329, d180795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d180329, d180795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d180336 q = 1) (hb : d180801 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d180336, d180801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d180336, d180801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40807 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d176852 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d180337 q = 1) (hb : d180802 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d180337, d180802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d180337, d180802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d180338 q = 1) (hb : d180803 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d180338, d180803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d180338, d180803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d180339 q = 1) (hb : d180804 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d180339, d180804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d180339, d180804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d180340 q = 1) (hb : d180805 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d180340, d180805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d180340, d180805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d180341 q = 1) (hb : d180806 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d180341, d180806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d180341, d180806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro40809 (p : Pattern) (ha : d180347 p = 1) (hb : d180812 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d180342 q = 1) (hb : d180807 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d180342, d180807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d180342, d180807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40808 q ha hb
  have h2 (q : Pattern) (ha : d180343 q = 1) (hb : d180808 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d180343, d180808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d180343, d180808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d180344 q = 1) (hb : d180809 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d180344, d180809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d180344, d180809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d180345 q = 1) (hb : d180810 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d180345, d180810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d180345, d180810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d180346 q = 1) (hb : d180811 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d180346, d180811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d180346, d180811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d180347 q = 1) (hb : d180812 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d180347, d180812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d180347, d180812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro40810 (p : Pattern) (ha : d178876 p = 1) (hb : d180821 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d176918 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d176927 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d176940 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d178871 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d178872 q = 1) (hb : d180817 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d178872, d180817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d178872, d180817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d176980 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d178873 q = 1) (hb : d180818 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d178873, d180818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d178873, d180818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d178874 q = 1) (hb : d180819 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d178874, d180819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d178874, d180819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d178875 q = 1) (hb : d180820 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d178875, d180820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d178875, d180820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d178876 q = 1) (hb : d180821 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d178876, d180821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d178876, d180821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro40811 (p : Pattern) (ha : d178886 p = 1) (hb : d180826 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d176918 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d176927 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d176940 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d178871 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d178872 q = 1) (hb : d180817 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d178872, d180817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d178872, d180817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d176980 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d178873 q = 1) (hb : d180818 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d178873, d180818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d178873, d180818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d178874 q = 1) (hb : d180819 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d178874, d180819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d178874, d180819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d178875 q = 1) (hb : d180820 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d178875, d180820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d178875, d180820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d176990 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d176995 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d176997 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d178881 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d178882 q = 1) (hb : d180822 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d178882, d180822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d178882, d180822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d177004 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d178883 q = 1) (hb : d180823 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d178883, d180823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d178883, d180823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d178884 q = 1) (hb : d180824 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d178884, d180824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d178884, d180824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d178885 q = 1) (hb : d180825 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d178885, d180825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d178885, d180825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d178886 q = 1) (hb : d180826 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d178886, d180826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d178886, d180826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro40812 (p : Pattern) (ha : d180354 p = 1) (hb : d180833 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d176997 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d178881 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d178882 q = 1) (hb : d180822 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d178882, d180822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d178882, d180822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d177004 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d178883 q = 1) (hb : d180823 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d178883, d180823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d178883, d180823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d178884 q = 1) (hb : d180831 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d178884, d180831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d178884, d180831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d178885 q = 1) (hb : d180832 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d178885, d180832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d178885, d180832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d180354 q = 1) (hb : d180833 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d180354, d180833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d180354, d180833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro40813 (p : Pattern) (ha : d180365 p = 1) (hb : d180843 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d177068 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d180360 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d180361 q = 1) (hb : d180839 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d180361, d180839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d180361, d180839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d177108 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d180362 q = 1) (hb : d180840 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d180362, d180840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d180362, d180840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d180363 q = 1) (hb : d180841 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d180363, d180841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d180363, d180841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d180364 q = 1) (hb : d180842 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d180364, d180842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d180364, d180842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d180365 q = 1) (hb : d180843 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d180365, d180843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d180365, d180843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro40814 (p : Pattern) (ha : d180371 p = 1) (hb : d180849 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d176910 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d178887 q = 1) (hb : d180827 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d178887, d180827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40810 q ha hb
    | true =>
      simp only [d178887, d180827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40811 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d177022 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d178888 q = 1) (hb : d180828 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d178888, d180828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d178888, d180828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d180352 q = 1) (hb : d180829 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d180352, d180829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d180352, d180829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d180353 q = 1) (hb : d180830 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d180353, d180830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d180353, d180830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d180355 q = 1) (hb : d180834 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d180355, d180834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d180355, d180834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40812 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d177031 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d180356 q = 1) (hb : d180835 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d180356, d180835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d180356, d180835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d180357 q = 1) (hb : d180836 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d180357, d180836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d180357, d180836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d180358 q = 1) (hb : d180837 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d180358, d180837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d180358, d180837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d180359 q = 1) (hb : d180838 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d180359, d180838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d180359, d180838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d180366 q = 1) (hb : d180844 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d180366, d180844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d180366, d180844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40813 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d177124 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d180367 q = 1) (hb : d180845 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d180367, d180845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d180367, d180845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d180368 q = 1) (hb : d180846 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d180368, d180846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d180368, d180846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d180369 q = 1) (hb : d180847 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d180369, d180847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d180369, d180847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d180370 q = 1) (hb : d180848 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d180370, d180848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d180370, d180848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d180371 q = 1) (hb : d180849 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d180371, d180849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d180371, d180849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro40815 (p : Pattern) (ha : d180377 p = 1) (hb : d180855 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d180372 q = 1) (hb : d180850 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d180372, d180850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d180372, d180850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40814 q ha hb
  have h2 (q : Pattern) (ha : d180373 q = 1) (hb : d180851 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d180373, d180851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d180373, d180851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d180374 q = 1) (hb : d180852 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d180374, d180852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d180374, d180852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d180375 q = 1) (hb : d180853 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d180375, d180853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d180375, d180853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d180376 q = 1) (hb : d180854 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d180376, d180854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d180376, d180854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d180377 q = 1) (hb : d180855 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d180377, d180855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d180377, d180855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro40816 (p : Pattern) (ha : d180383 p = 1) (hb : d180861 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d161075 q = 1) (hb : d180690 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d161075, d180690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40785 q ha hb
    | true =>
      simp only [d161075, d180690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40791 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d180291 q = 1) (hb : d180730 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d180291, d180730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d180291, d180730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40797 q ha hb
  have h3 (q : Pattern) (ha : d180292 q = 1) (hb : d180731 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d180292, d180731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d180292, d180731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d180319 q = 1) (hb : d180771 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d180319, d180771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d180319, d180771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40803 q ha hb
  have h5 (q : Pattern) (ha : d180320 q = 1) (hb : d180772 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d180320, d180772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d180320, d180772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d180321 q = 1) (hb : d180773 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d180321, d180773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d180321, d180773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d180348 q = 1) (hb : d180813 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d180348, d180813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d180348, d180813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40809 q ha hb
  have h8 (q : Pattern) (ha : d180349 q = 1) (hb : d180814 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d180349, d180814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d180349, d180814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d180350 q = 1) (hb : d180815 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d180350, d180815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d180350, d180815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d180351 q = 1) (hb : d180816 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d180351, d180816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d180351, d180816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d180378 q = 1) (hb : d180856 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d180378, d180856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d180378, d180856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40815 q ha hb
  have h12 (q : Pattern) (ha : d180379 q = 1) (hb : d180857 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d180379, d180857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d180379, d180857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d180380 q = 1) (hb : d180858 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d180380, d180858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d180380, d180858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d180381 q = 1) (hb : d180859 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d180381, d180859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d180381, d180859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d180382 q = 1) (hb : d180860 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d180382, d180860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d180382, d180860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d180383 q = 1) (hb : d180861 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d180383, d180861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d180383, d180861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro40817 (p : Pattern) (ha : d180389 p = 1) (hb : d180867 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d180384 q = 1) (hb : d180862 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d180384, d180862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40816 q ha hb
    | true =>
      simp only [d180384, d180862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d180385 q = 1) (hb : d180863 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d180385, d180863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d180385, d180863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d180386 q = 1) (hb : d180864 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d180386, d180864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d180386, d180864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d180387 q = 1) (hb : d180865 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d180387, d180865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d180387, d180865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d180388 q = 1) (hb : d180866 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d180388, d180866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d180388, d180866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d180389 q = 1) (hb : d180867 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d180389, d180867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d180389, d180867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro40818 (p : Pattern) (ha : d180395 p = 1) (hb : d180873 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d180390 q = 1) (hb : d180868 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d180390, d180868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40817 q ha hb
    | true =>
      simp only [d180390, d180868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d180391 q = 1) (hb : d180869 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d180391, d180869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d180391, d180869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d180392 q = 1) (hb : d180870 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d180392, d180870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d180392, d180870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d180393 q = 1) (hb : d180871 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d180393, d180871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d180393, d180871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d180394 q = 1) (hb : d180872 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d180394, d180872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d180394, d180872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d180395 q = 1) (hb : d180873 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d180395, d180873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d180395, d180873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro40819 (p : Pattern) (ha : d180401 p = 1) (hb : d180879 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d180396 q = 1) (hb : d180874 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d180396, d180874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40818 q ha hb
    | true =>
      simp only [d180396, d180874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d180397 q = 1) (hb : d180875 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d180397, d180875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d180397, d180875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d180398 q = 1) (hb : d180876 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d180398, d180876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d180398, d180876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d180399 q = 1) (hb : d180877 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d180399, d180877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d180399, d180877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d180400 q = 1) (hb : d180878 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d180400, d180878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d180400, d180878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d180401 q = 1) (hb : d180879 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d180401, d180879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d180401, d180879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro40820 (p : Pattern) (ha : d180407 p = 1) (hb : d180885 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d180402 q = 1) (hb : d180880 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d180402, d180880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40819 q ha hb
    | true =>
      simp only [d180402, d180880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d180403 q = 1) (hb : d180881 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d180403, d180881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d180403, d180881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d180404 q = 1) (hb : d180882 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d180404, d180882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d180404, d180882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d180405 q = 1) (hb : d180883 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d180405, d180883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d180405, d180883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d180406 q = 1) (hb : d180884 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d180406, d180884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d180406, d180884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d180407 q = 1) (hb : d180885 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d180407, d180885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d180407, d180885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro40821 (p : Pattern) (ha : d180413 p = 1) (hb : d180891 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d180408 q = 1) (hb : d180886 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d180408, d180886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40820 q ha hb
    | true =>
      simp only [d180408, d180886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d180409 q = 1) (hb : d180887 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d180409, d180887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d180409, d180887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d180410 q = 1) (hb : d180888 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d180410, d180888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d180410, d180888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d180411 q = 1) (hb : d180889 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d180411, d180889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d180411, d180889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d180412 q = 1) (hb : d180890 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d180412, d180890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d180412, d180890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d180413 q = 1) (hb : d180891 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d180413, d180891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d180413, d180891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro40822 (p : Pattern) (ha : d180419 p = 1) (hb : d180897 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d180414 q = 1) (hb : d180892 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d180414, d180892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40821 q ha hb
    | true =>
      simp only [d180414, d180892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d180415 q = 1) (hb : d180893 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d180415, d180893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d180415, d180893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d180416 q = 1) (hb : d180894 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d180416, d180894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d180416, d180894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d180417 q = 1) (hb : d180895 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d180417, d180895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d180417, d180895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d180418 q = 1) (hb : d180896 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d180418, d180896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d180418, d180896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d180419 q = 1) (hb : d180897 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d180419, d180897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d180419, d180897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro40823 (p : Pattern) (ha : d180425 p = 1) (hb : d180903 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d180420 q = 1) (hb : d180898 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d180420, d180898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40822 q ha hb
    | true =>
      simp only [d180420, d180898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d180421 q = 1) (hb : d180899 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d180421, d180899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d180421, d180899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d180422 q = 1) (hb : d180900 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d180422, d180900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d180422, d180900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d180423 q = 1) (hb : d180901 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d180423, d180901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d180423, d180901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d180424 q = 1) (hb : d180902 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d180424, d180902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d180424, d180902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d180425 q = 1) (hb : d180903 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d180425, d180903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d180425, d180903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro40824 (p : Pattern) (ha : d128482 p = 1) (hb : d180907 p = 1) : d128482 p = 1 := by
  have h0 (q : Pattern) (ha : d128482 q = 1) (hb : d180907 q = 1) : d128482 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro40825 (p : Pattern) (ha : d171287 p = 1) (hb : d180907 p = 1) : d171287 p = 1 := by
  have h0 (q : Pattern) (ha : d171287 q = 1) (hb : d180907 q = 1) : d171287 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro40826 (p : Pattern) (ha : d17564 p = 1) (hb : d180908 p = 1) : d180912 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d66 q = 1) : d66 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d25 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d67 q = 1) (hb : d131097 q = 1) : d18534 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d67, d131097, d18534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d67, d131097, d18534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d17561 q = 1) (hb : d180908 q = 1) : d180909 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17561, d180908, d180909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17561, d180908, d180909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d17562 q = 1) (hb : d180908 q = 1) : d180910 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17562, d180910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17562, d180910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17563 q = 1) (hb : d180908 q = 1) : d180911 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17563, d180911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17563, d180911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d17564 q = 1) (hb : d180908 q = 1) : d180912 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d17564, d180912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17564, d180912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro40827 (p : Pattern) (ha : d17570 p = 1) (hb : d180908 p = 1) : d180918 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17565 q = 1) (hb : d180908 q = 1) : d180913 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17565, d180913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40826 q ha hb
    | true =>
      simp only [d17565, d180913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17566 q = 1) (hb : d180908 q = 1) : d180914 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17566, d180914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17566, d180914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17567 q = 1) (hb : d180908 q = 1) : d180915 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17567, d180915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17567, d180915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17568 q = 1) (hb : d180908 q = 1) : d180916 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17568, d180916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17568, d180916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d17569 q = 1) (hb : d180908 q = 1) : d180917 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17569, d180917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17569, d180917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d17570 q = 1) (hb : d180908 q = 1) : d180918 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d17570, d180918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17570, d180918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro40828 (p : Pattern) (ha : d17576 p = 1) (hb : d180908 p = 1) : d180924 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17571 q = 1) (hb : d180908 q = 1) : d180919 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17571, d180919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40827 q ha hb
    | true =>
      simp only [d17571, d180919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17572 q = 1) (hb : d180908 q = 1) : d180920 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17572, d180920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17572, d180920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17573 q = 1) (hb : d180908 q = 1) : d180921 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17573, d180921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17573, d180921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17574 q = 1) (hb : d180908 q = 1) : d180922 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17574, d180922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17574, d180922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d17575 q = 1) (hb : d180908 q = 1) : d180923 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17575, d180923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17575, d180923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d17576 q = 1) (hb : d180908 q = 1) : d180924 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17576, d180924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17576, d180924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro40829 (p : Pattern) (ha : d17582 p = 1) (hb : d180908 p = 1) : d180930 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17577 q = 1) (hb : d180908 q = 1) : d180925 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17577, d180925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40828 q ha hb
    | true =>
      simp only [d17577, d180925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17578 q = 1) (hb : d180908 q = 1) : d180926 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d17578, d180926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d17578, d180926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d17579 q = 1) (hb : d180908 q = 1) : d180927 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d17579, d180927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17579, d180927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17580 q = 1) (hb : d180908 q = 1) : d180928 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d17580, d180928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17580, d180928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17581 q = 1) (hb : d180908 q = 1) : d180929 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d17581, d180929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17581, d180929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17582 q = 1) (hb : d180908 q = 1) : d180930 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d17582, d180930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17582, d180930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro40830 (p : Pattern) (ha : d17588 p = 1) (hb : d180908 p = 1) : d180936 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17583 q = 1) (hb : d180908 q = 1) : d180931 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d17583, d180931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17583, d180931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40829 q ha hb
  have h2 (q : Pattern) (ha : d17584 q = 1) (hb : d180908 q = 1) : d180932 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d17584, d180932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d17584, d180932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d17585 q = 1) (hb : d180908 q = 1) : d180933 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d17585, d180933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17585, d180933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17586 q = 1) (hb : d180908 q = 1) : d180934 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d17586, d180934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17586, d180934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d17587 q = 1) (hb : d180908 q = 1) : d180935 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d17587, d180935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17587, d180935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d17588 q = 1) (hb : d180908 q = 1) : d180936 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d17588, d180936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17588, d180936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro40831 (p : Pattern) (ha : d17596 p = 1) (hb : d180908 p = 1) : d180944 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d226 q = 1) : d226 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d139 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d227 q = 1) (hb : d131097 q = 1) : d18571 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d227, d131097, d18571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d227, d131097, d18571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d17593 q = 1) (hb : d180908 q = 1) : d180941 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17593, d180908, d180941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17593, d180908, d180941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d17594 q = 1) (hb : d180908 q = 1) : d180942 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17594, d180942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17594, d180942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1 q = 1) (hb : d66 q = 1) : d66 q = 1 := by
    exact hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d25 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d67 q = 1) (hb : d131097 q = 1) : d18534 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d67, d131097, d18534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d67, d131097, d18534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d17561 q = 1) (hb : d180908 q = 1) : d180909 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17561, d180908, d180909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d17561, d180908, d180909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h11 (q : Pattern) (ha : d17562 q = 1) (hb : d180908 q = 1) : d180910 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17562, d180910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d17562, d180910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h12 (q : Pattern) (ha : d17595 q = 1) (hb : d180908 q = 1) : d180943 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17595, d180943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17595, d180943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d17563 q = 1) (hb : d180908 q = 1) : d180911 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17563, d180911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d17563, d180911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h14 (q : Pattern) (ha : d17596 q = 1) (hb : d180908 q = 1) : d180944 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d17596, d180944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d17596, d180944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h14 p ha hb
theorem andIntro40832 (p : Pattern) (ha : d17602 p = 1) (hb : d180908 p = 1) : d180950 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17597 q = 1) (hb : d180908 q = 1) : d180945 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17597, d180945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40831 q ha hb
    | true =>
      simp only [d17597, d180945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40826 q ha hb
  have h2 (q : Pattern) (ha : d17598 q = 1) (hb : d180908 q = 1) : d180946 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17598, d180946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17598, d180946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17599 q = 1) (hb : d180908 q = 1) : d180947 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17599, d180947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17599, d180947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17565 q = 1) (hb : d180908 q = 1) : d180913 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17565, d180913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40826 q ha hb
    | true =>
      simp only [d17565, d180913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d17566 q = 1) (hb : d180908 q = 1) : d180914 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17566, d180914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17566, d180914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17567 q = 1) (hb : d180908 q = 1) : d180915 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17567, d180915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17567, d180915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17600 q = 1) (hb : d180908 q = 1) : d180948 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17600, d180948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17600, d180948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17568 q = 1) (hb : d180908 q = 1) : d180916 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17568, d180916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17568, d180916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d17601 q = 1) (hb : d180908 q = 1) : d180949 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17601, d180949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17601, d180949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d17602 q = 1) (hb : d180908 q = 1) : d180950 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d17602, d180950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d17602, d180950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro40833 (p : Pattern) (ha : d17608 p = 1) (hb : d180908 p = 1) : d180956 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17603 q = 1) (hb : d180908 q = 1) : d180951 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17603, d180951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40832 q ha hb
    | true =>
      simp only [d17603, d180951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17604 q = 1) (hb : d180908 q = 1) : d180952 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17604, d180952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17604, d180952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17571 q = 1) (hb : d180908 q = 1) : d180919 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17571, d180919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40827 q ha hb
    | true =>
      simp only [d17571, d180919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17572 q = 1) (hb : d180908 q = 1) : d180920 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17572, d180920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17572, d180920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17605 q = 1) (hb : d180908 q = 1) : d180953 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17605, d180953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17605, d180953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17606 q = 1) (hb : d180908 q = 1) : d180954 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17606, d180954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17606, d180954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d17607 q = 1) (hb : d180908 q = 1) : d180955 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17607, d180955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17607, d180955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d17608 q = 1) (hb : d180908 q = 1) : d180956 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17608, d180956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17608, d180956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro40834 (p : Pattern) (ha : d60563 p = 1) (hb : d180908 p = 1) : d180962 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17609 q = 1) (hb : d180908 q = 1) : d180957 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17609, d180957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40833 q ha hb
    | true =>
      simp only [d17609, d180957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40828 q ha hb
  have h2 (q : Pattern) (ha : d60559 q = 1) (hb : d180908 q = 1) : d180958 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d60559, d180958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d60559, d180958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d17577 q = 1) (hb : d180908 q = 1) : d180925 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17577, d180925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40828 q ha hb
    | true =>
      simp only [d17577, d180925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17578 q = 1) (hb : d180908 q = 1) : d180926 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d17578, d180926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17578, d180926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d60560 q = 1) (hb : d180908 q = 1) : d180959 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d60560, d180959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d60560, d180959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d60561 q = 1) (hb : d180908 q = 1) : d180960 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d60561, d180960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d60561, d180960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d60562 q = 1) (hb : d180908 q = 1) : d180961 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d60562, d180961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d60562, d180961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d60563 q = 1) (hb : d180908 q = 1) : d180962 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d60563, d180962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d60563, d180962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro40835 (p : Pattern) (ha : d60569 p = 1) (hb : d180908 p = 1) : d180968 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d60564 q = 1) (hb : d180908 q = 1) : d180963 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d60564, d180963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d60564, d180963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40834 q ha hb
  have h2 (q : Pattern) (ha : d60565 q = 1) (hb : d180908 q = 1) : d180964 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d60565, d180964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d60565, d180964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d60566 q = 1) (hb : d180908 q = 1) : d180965 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d60566, d180965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d60566, d180965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d60567 q = 1) (hb : d180908 q = 1) : d180966 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d60567, d180966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d60567, d180966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d60568 q = 1) (hb : d180908 q = 1) : d180967 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d60568, d180967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d60568, d180967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d60569 q = 1) (hb : d180908 q = 1) : d180968 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d60569, d180968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d60569, d180968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro40836 (p : Pattern) (ha : d17696 p = 1) (hb : d180908 p = 1) : d181010 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17577 q = 1) (hb : d180908 q = 1) : d180925 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17577, d180925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40828 q ha hb
    | true =>
      simp only [d17577, d180925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17692 q = 1) (hb : d180908 q = 1) : d181006 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d17692, d181006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17692, d181006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17693 q = 1) (hb : d180908 q = 1) : d181007 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d17693, d181007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17693, d181007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17694 q = 1) (hb : d180908 q = 1) : d181008 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d17694, d181008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17694, d181008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17695 q = 1) (hb : d180908 q = 1) : d181009 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d17695, d181009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17695, d181009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17696 q = 1) (hb : d180908 q = 1) : d181010 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d17696, d181010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17696, d181010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro40837 (p : Pattern) (ha : d17649 p = 1) (hb : d180908 p = 1) : d180980 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d412 q = 1) : d412 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d319 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d413 q = 1) (hb : d131097 q = 1) : d18631 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d413, d131097, d18631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d413, d131097, d18631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d17643 q = 1) (hb : d180908 q = 1) : d180974 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17643, d180908, d180974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17643, d180908, d180974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d17644 q = 1) (hb : d180908 q = 1) : d180975 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17644, d180975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17644, d180975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1 q = 1) (hb : d226 q = 1) : d226 q = 1 := by
    exact hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d139 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d227 q = 1) (hb : d131097 q = 1) : d18571 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d227, d131097, d18571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d227, d131097, d18571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d17593 q = 1) (hb : d180908 q = 1) : d180941 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17593, d180908, d180941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d17593, d180908, d180941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h11 (q : Pattern) (ha : d17594 q = 1) (hb : d180908 q = 1) : d180942 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17594, d180942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d17594, d180942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h12 (q : Pattern) (ha : d17645 q = 1) (hb : d180908 q = 1) : d180976 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17645, d180976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17645, d180976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d1 q = 1) (hb : d12599 q = 1) : d12599 q = 1 := by
    exact hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d9382 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d12600 q = 1) (hb : d131097 q = 1) : d18635 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d12600, d131097, d18635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d12600, d131097, d18635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d17646 q = 1) (hb : d180908 q = 1) : d180977 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17646, d180908, d180977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d17646, d180908, d180977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h17 (q : Pattern) (ha : d17647 q = 1) (hb : d180908 q = 1) : d180978 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17647, d180978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d17647, d180978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h18 (q : Pattern) (ha : d1 q = 1) (hb : d66 q = 1) : d66 q = 1 := by
    exact hb
  have h19 (q : Pattern) (ha : d0 q = 1) (hb : d25 q = 1) : d0 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d67 q = 1) (hb : d131097 q = 1) : d18534 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d67, d131097, d18534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
    | true =>
      simp only [d67, d131097, d18534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
  have h21 (q : Pattern) (ha : d17561 q = 1) (hb : d180908 q = 1) : d180909 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17561, d180908, d180909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d17561, d180908, d180909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h22 (q : Pattern) (ha : d17562 q = 1) (hb : d180908 q = 1) : d180910 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17562, d180910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d17562, d180910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h23 (q : Pattern) (ha : d17648 q = 1) (hb : d180908 q = 1) : d180979 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17648, d180979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d17648, d180979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d17649 q = 1) (hb : d180908 q = 1) : d180980 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d17649, d180980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d17649, d180980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  exact h24 p ha hb
theorem andIntro40838 (p : Pattern) (ha : d17655 p = 1) (hb : d180908 p = 1) : d180986 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17650 q = 1) (hb : d180908 q = 1) : d180981 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17650, d180981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40837 q ha hb
    | true =>
      simp only [d17650, d180981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40831 q ha hb
  have h2 (q : Pattern) (ha : d17651 q = 1) (hb : d180908 q = 1) : d180982 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17651, d180982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17651, d180982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17652 q = 1) (hb : d180908 q = 1) : d180983 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17652, d180983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17652, d180983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17597 q = 1) (hb : d180908 q = 1) : d180945 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17597, d180945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40831 q ha hb
    | true =>
      simp only [d17597, d180945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40826 q ha hb
  have h5 (q : Pattern) (ha : d17598 q = 1) (hb : d180908 q = 1) : d180946 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17598, d180946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17598, d180946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17599 q = 1) (hb : d180908 q = 1) : d180947 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17599, d180947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17599, d180947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17653 q = 1) (hb : d180908 q = 1) : d180984 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17653, d180984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17653, d180984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17565 q = 1) (hb : d180908 q = 1) : d180913 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17565, d180913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40826 q ha hb
    | true =>
      simp only [d17565, d180913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d17566 q = 1) (hb : d180908 q = 1) : d180914 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17566, d180914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17566, d180914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d17567 q = 1) (hb : d180908 q = 1) : d180915 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17567, d180915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17567, d180915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d17600 q = 1) (hb : d180908 q = 1) : d180948 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17600, d180948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17600, d180948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d17654 q = 1) (hb : d180908 q = 1) : d180985 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17654, d180985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17654, d180985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d17655 q = 1) (hb : d180908 q = 1) : d180986 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d17655, d180986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d17655, d180986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro40839 (p : Pattern) (ha : d17661 p = 1) (hb : d180908 p = 1) : d180992 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17656 q = 1) (hb : d180908 q = 1) : d180987 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17656, d180987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40838 q ha hb
    | true =>
      simp only [d17656, d180987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17657 q = 1) (hb : d180908 q = 1) : d180988 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17657, d180988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17657, d180988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17603 q = 1) (hb : d180908 q = 1) : d180951 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17603, d180951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40832 q ha hb
    | true =>
      simp only [d17603, d180951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17604 q = 1) (hb : d180908 q = 1) : d180952 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17604, d180952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17604, d180952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17658 q = 1) (hb : d180908 q = 1) : d180989 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17658, d180989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17658, d180989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17659 q = 1) (hb : d180908 q = 1) : d180990 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17659, d180990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17659, d180990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d17660 q = 1) (hb : d180908 q = 1) : d180991 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17660, d180991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17660, d180991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d17661 q = 1) (hb : d180908 q = 1) : d180992 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17661, d180992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17661, d180992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro40840 (p : Pattern) (ha : d17684 p = 1) (hb : d180908 p = 1) : d180998 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17603 q = 1) (hb : d180908 q = 1) : d180951 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17603, d180951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40832 q ha hb
    | true =>
      simp only [d17603, d180951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17604 q = 1) (hb : d180908 q = 1) : d180952 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17604, d180952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17604, d180952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17681 q = 1) (hb : d180908 q = 1) : d180995 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17681, d180995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17681, d180995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17682 q = 1) (hb : d180908 q = 1) : d180996 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17682, d180996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17682, d180996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d17683 q = 1) (hb : d180908 q = 1) : d180997 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17683, d180997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17683, d180997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d17684 q = 1) (hb : d180908 q = 1) : d180998 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17684, d180998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17684, d180998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro40841 (p : Pattern) (ha : d129315 p = 1) (hb : d180908 p = 1) : d181004 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17662 q = 1) (hb : d180908 q = 1) : d180993 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17662, d180993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40839 q ha hb
    | true =>
      simp only [d17662, d180993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40833 q ha hb
  have h2 (q : Pattern) (ha : d129311 q = 1) (hb : d180908 q = 1) : d180994 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d129311, d180994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129311, d180994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d17685 q = 1) (hb : d180908 q = 1) : d180999 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17685, d180999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40840 q ha hb
    | true =>
      simp only [d17685, d180999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17686 q = 1) (hb : d180908 q = 1) : d181000 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d17686, d181000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17686, d181000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d129312 q = 1) (hb : d180908 q = 1) : d181001 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d129312, d181001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129312, d181001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129313 q = 1) (hb : d180908 q = 1) : d181002 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d129313, d181002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129313, d181002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d129314 q = 1) (hb : d180908 q = 1) : d181003 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d129314, d181003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129314, d181003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d129315 q = 1) (hb : d180908 q = 1) : d181004 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d129315, d181004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129315, d181004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro40842 (p : Pattern) (ha : d129321 p = 1) (hb : d180908 p = 1) : d181016 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129316 q = 1) (hb : d180908 q = 1) : d181005 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d129316, d181005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129316, d181005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40841 q ha hb
  have h2 (q : Pattern) (ha : d17697 q = 1) (hb : d180908 q = 1) : d181011 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d17697, d181011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17697, d181011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40836 q ha hb
  have h3 (q : Pattern) (ha : d129317 q = 1) (hb : d180908 q = 1) : d181012 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d129317, d181012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129317, d181012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d129318 q = 1) (hb : d180908 q = 1) : d181013 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d129318, d181013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129318, d181013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d129319 q = 1) (hb : d180908 q = 1) : d181014 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d129319, d181014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129319, d181014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d129320 q = 1) (hb : d180908 q = 1) : d181015 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d129320, d181015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129320, d181015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d129321 q = 1) (hb : d180908 q = 1) : d181016 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d129321, d181016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129321, d181016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro40843 (p : Pattern) (ha : d129327 p = 1) (hb : d180908 p = 1) : d181022 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17589 q = 1) (hb : d180908 q = 1) : d180937 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d17589, d180937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17589, d180937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40830 q ha hb
  have h2 (q : Pattern) (ha : d17590 q = 1) (hb : d180908 q = 1) : d180938 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d17590, d180938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17590, d180938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17591 q = 1) (hb : d180908 q = 1) : d180939 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d17591, d180939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17591, d180939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17592 q = 1) (hb : d180908 q = 1) : d180940 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d17592, d180940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17592, d180940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d60570 q = 1) (hb : d180908 q = 1) : d180969 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d60570, d180969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d60570, d180969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40835 q ha hb
  have h6 (q : Pattern) (ha : d60571 q = 1) (hb : d180908 q = 1) : d180970 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d60571, d180970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d60571, d180970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d60572 q = 1) (hb : d180908 q = 1) : d180971 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d60572, d180971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d60572, d180971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d60573 q = 1) (hb : d180908 q = 1) : d180972 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d60573, d180972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d60573, d180972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d60574 q = 1) (hb : d180908 q = 1) : d180973 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d60574, d180973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d60574, d180973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d129322 q = 1) (hb : d180908 q = 1) : d181017 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d129322, d181017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129322, d181017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40842 q ha hb
  have h11 (q : Pattern) (ha : d129323 q = 1) (hb : d180908 q = 1) : d181018 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d129323, d181018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129323, d181018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d129324 q = 1) (hb : d180908 q = 1) : d181019 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d129324, d181019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129324, d181019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d129325 q = 1) (hb : d180908 q = 1) : d181020 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d129325, d181020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129325, d181020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d129326 q = 1) (hb : d180908 q = 1) : d181021 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d129326, d181021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129326, d181021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d129327 q = 1) (hb : d180908 q = 1) : d181022 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d129327, d181022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d129327, d181022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro40844 (p : Pattern) (ha : d17740 p = 1) (hb : d180908 p = 1) : d181054 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17597 q = 1) (hb : d180908 q = 1) : d180945 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17597, d180945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40831 q ha hb
    | true =>
      simp only [d17597, d180945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40826 q ha hb
  have h2 (q : Pattern) (ha : d17598 q = 1) (hb : d180908 q = 1) : d180946 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17598, d180946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17598, d180946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17599 q = 1) (hb : d180908 q = 1) : d180947 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17599, d180947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17599, d180947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17730 q = 1) (hb : d180908 q = 1) : d181044 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17730, d181044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17730, d181044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d17739 q = 1) (hb : d180908 q = 1) : d181053 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17739, d181053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17739, d181053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d17740 q = 1) (hb : d180908 q = 1) : d181054 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d17740, d181054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17740, d181054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro40845 (p : Pattern) (ha : d17792 p = 1) (hb : d180908 p = 1) : d181077 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17741 q = 1) (hb : d180908 q = 1) : d181055 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17741, d181055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40844 q ha hb
    | true =>
      simp only [d17741, d181055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17742 q = 1) (hb : d180908 q = 1) : d181056 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17742, d181056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17742, d181056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17789 q = 1) (hb : d180908 q = 1) : d181074 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17789, d181074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17789, d181074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17790 q = 1) (hb : d180908 q = 1) : d181075 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17790, d181075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17790, d181075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d17791 q = 1) (hb : d180908 q = 1) : d181076 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17791, d181076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17791, d181076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d17792 q = 1) (hb : d180908 q = 1) : d181077 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17792, d181077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17792, d181077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro40846 (p : Pattern) (ha : d17798 p = 1) (hb : d180908 p = 1) : d181083 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17793 q = 1) (hb : d180908 q = 1) : d181078 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17793, d181078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40845 q ha hb
    | true =>
      simp only [d17793, d181078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17794 q = 1) (hb : d180908 q = 1) : d181079 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d17794, d181079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17794, d181079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17795 q = 1) (hb : d180908 q = 1) : d181080 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d17795, d181080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17795, d181080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17796 q = 1) (hb : d180908 q = 1) : d181081 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d17796, d181081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17796, d181081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17797 q = 1) (hb : d180908 q = 1) : d181082 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d17797, d181082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17797, d181082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17798 q = 1) (hb : d180908 q = 1) : d181083 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d17798, d181083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17798, d181083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro40847 (p : Pattern) (ha : d17717 p = 1) (hb : d180908 p = 1) : d181031 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d659 q = 1) : d659 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d543 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d660 q = 1) (hb : d131097 q = 1) : d18708 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d660, d131097, d18708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d660, d131097, d18708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d17709 q = 1) (hb : d180908 q = 1) : d181023 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17709, d180908, d181023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17709, d180908, d181023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d17710 q = 1) (hb : d180908 q = 1) : d181024 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17710, d181024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17710, d181024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1 q = 1) (hb : d16156 q = 1) : d16156 q = 1 := by
    exact hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d9458 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d16157 q = 1) (hb : d131097 q = 1) : d18711 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d16157, d131097, d18711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d16157, d131097, d18711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d17711 q = 1) (hb : d180908 q = 1) : d181025 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17711, d180908, d181025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d17711, d180908, d181025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h11 (q : Pattern) (ha : d17712 q = 1) (hb : d180908 q = 1) : d181026 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17712, d181026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d17712, d181026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h12 (q : Pattern) (ha : d17713 q = 1) (hb : d180908 q = 1) : d181027 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17713, d181027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17713, d181027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d1 q = 1) (hb : d12858 q = 1) : d12858 q = 1 := by
    exact hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d9468 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d12859 q = 1) (hb : d131097 q = 1) : d18715 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d12859, d131097, d18715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d12859, d131097, d18715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d17714 q = 1) (hb : d180908 q = 1) : d181028 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17714, d180908, d181028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d17714, d180908, d181028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h17 (q : Pattern) (ha : d17715 q = 1) (hb : d180908 q = 1) : d181029 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17715, d181029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d17715, d181029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h18 (q : Pattern) (ha : d1 q = 1) (hb : d12599 q = 1) : d12599 q = 1 := by
    exact hb
  have h19 (q : Pattern) (ha : d0 q = 1) (hb : d9382 q = 1) : d0 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d12600 q = 1) (hb : d131097 q = 1) : d18635 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d12600, d131097, d18635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
    | true =>
      simp only [d12600, d131097, d18635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
  have h21 (q : Pattern) (ha : d17646 q = 1) (hb : d180908 q = 1) : d180977 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17646, d180908, d180977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d17646, d180908, d180977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h22 (q : Pattern) (ha : d17647 q = 1) (hb : d180908 q = 1) : d180978 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17647, d180978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d17647, d180978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h23 (q : Pattern) (ha : d17716 q = 1) (hb : d180908 q = 1) : d181030 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17716, d181030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d17716, d181030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d17717 q = 1) (hb : d180908 q = 1) : d181031 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d17717, d181031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d17717, d181031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  exact h24 p ha hb
theorem andIntro40848 (p : Pattern) (ha : d17721 p = 1) (hb : d180908 p = 1) : d181035 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d12599 q = 1) : d12599 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d9382 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12600 q = 1) (hb : d131097 q = 1) : d18635 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d12600, d131097, d18635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d12600, d131097, d18635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d17646 q = 1) (hb : d180908 q = 1) : d180977 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17646, d180908, d180977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17646, d180908, d180977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d17647 q = 1) (hb : d180908 q = 1) : d180978 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17647, d180978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17647, d180978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1 q = 1) (hb : d66 q = 1) : d66 q = 1 := by
    exact hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d25 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d67 q = 1) (hb : d131097 q = 1) : d18534 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d67, d131097, d18534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d67, d131097, d18534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d17561 q = 1) (hb : d180908 q = 1) : d180909 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17561, d180908, d180909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d17561, d180908, d180909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h11 (q : Pattern) (ha : d17562 q = 1) (hb : d180908 q = 1) : d180910 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17562, d180910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d17562, d180910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h12 (q : Pattern) (ha : d17648 q = 1) (hb : d180908 q = 1) : d180979 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17648, d180979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17648, d180979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d17563 q = 1) (hb : d180908 q = 1) : d180911 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17563, d180911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d17563, d180911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h14 (q : Pattern) (ha : d17721 q = 1) (hb : d180908 q = 1) : d181035 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d17721, d181035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d17721, d181035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h14 p ha hb
theorem andIntro40849 (p : Pattern) (ha : d17727 p = 1) (hb : d180908 p = 1) : d181041 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17718 q = 1) (hb : d180908 q = 1) : d181032 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17718, d181032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40847 q ha hb
    | true =>
      simp only [d17718, d181032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40837 q ha hb
  have h2 (q : Pattern) (ha : d17719 q = 1) (hb : d180908 q = 1) : d181033 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17719, d181033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17719, d181033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17720 q = 1) (hb : d180908 q = 1) : d181034 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17720, d181034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17720, d181034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17722 q = 1) (hb : d180908 q = 1) : d181036 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17722, d181036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40837 q ha hb
    | true =>
      simp only [d17722, d181036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40848 q ha hb
  have h5 (q : Pattern) (ha : d17723 q = 1) (hb : d180908 q = 1) : d181037 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17723, d181037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17723, d181037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17724 q = 1) (hb : d180908 q = 1) : d181038 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17724, d181038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17724, d181038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17725 q = 1) (hb : d180908 q = 1) : d181039 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17725, d181039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17725, d181039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17650 q = 1) (hb : d180908 q = 1) : d180981 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17650, d180981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40837 q ha hb
    | true =>
      simp only [d17650, d180981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40831 q ha hb
  have h9 (q : Pattern) (ha : d17651 q = 1) (hb : d180908 q = 1) : d180982 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17651, d180982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17651, d180982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d17652 q = 1) (hb : d180908 q = 1) : d180983 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17652, d180983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17652, d180983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d17597 q = 1) (hb : d180908 q = 1) : d180945 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17597, d180945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40831 q ha hb
    | true =>
      simp only [d17597, d180945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40826 q ha hb
  have h12 (q : Pattern) (ha : d17598 q = 1) (hb : d180908 q = 1) : d180946 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17598, d180946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17598, d180946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d17599 q = 1) (hb : d180908 q = 1) : d180947 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17599, d180947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17599, d180947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d17653 q = 1) (hb : d180908 q = 1) : d180984 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17653, d180984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d17653, d180984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d17726 q = 1) (hb : d180908 q = 1) : d181040 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17726, d181040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17726, d181040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d17727 q = 1) (hb : d180908 q = 1) : d181041 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d17727, d181041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d17727, d181041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro40850 (p : Pattern) (ha : d17732 p = 1) (hb : d180908 p = 1) : d181046 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17650 q = 1) (hb : d180908 q = 1) : d180981 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17650, d180981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40837 q ha hb
    | true =>
      simp only [d17650, d180981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40831 q ha hb
  have h2 (q : Pattern) (ha : d17651 q = 1) (hb : d180908 q = 1) : d180982 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17651, d180982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17651, d180982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17652 q = 1) (hb : d180908 q = 1) : d180983 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17652, d180983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17652, d180983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17597 q = 1) (hb : d180908 q = 1) : d180945 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17597, d180945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40831 q ha hb
    | true =>
      simp only [d17597, d180945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40826 q ha hb
  have h5 (q : Pattern) (ha : d17598 q = 1) (hb : d180908 q = 1) : d180946 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17598, d180946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17598, d180946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17599 q = 1) (hb : d180908 q = 1) : d180947 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17599, d180947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17599, d180947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17653 q = 1) (hb : d180908 q = 1) : d180984 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17653, d180984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17653, d180984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17730 q = 1) (hb : d180908 q = 1) : d181044 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17730, d181044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17730, d181044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d17731 q = 1) (hb : d180908 q = 1) : d181045 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17731, d181045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17731, d181045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d17732 q = 1) (hb : d180908 q = 1) : d181046 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d17732, d181046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d17732, d181046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro40851 (p : Pattern) (ha : d17738 p = 1) (hb : d180908 p = 1) : d181052 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17728 q = 1) (hb : d180908 q = 1) : d181042 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17728, d181042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40849 q ha hb
    | true =>
      simp only [d17728, d181042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17729 q = 1) (hb : d180908 q = 1) : d181043 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17729, d181043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17729, d181043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17733 q = 1) (hb : d180908 q = 1) : d181047 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17733, d181047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40850 q ha hb
    | true =>
      simp only [d17733, d181047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17734 q = 1) (hb : d180908 q = 1) : d181048 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17734, d181048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17734, d181048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17735 q = 1) (hb : d180908 q = 1) : d181049 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17735, d181049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17735, d181049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17736 q = 1) (hb : d180908 q = 1) : d181050 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17736, d181050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17736, d181050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d17737 q = 1) (hb : d180908 q = 1) : d181051 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17737, d181051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17737, d181051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d17738 q = 1) (hb : d180908 q = 1) : d181052 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17738, d181052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17738, d181052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro40852 (p : Pattern) (ha : d17746 p = 1) (hb : d180908 p = 1) : d181060 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17733 q = 1) (hb : d180908 q = 1) : d181047 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17733, d181047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40850 q ha hb
    | true =>
      simp only [d17733, d181047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17734 q = 1) (hb : d180908 q = 1) : d181048 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17734, d181048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17734, d181048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17741 q = 1) (hb : d180908 q = 1) : d181055 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17741, d181055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40844 q ha hb
    | true =>
      simp only [d17741, d181055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17742 q = 1) (hb : d180908 q = 1) : d181056 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17742, d181056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17742, d181056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17743 q = 1) (hb : d180908 q = 1) : d181057 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17743, d181057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17743, d181057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17744 q = 1) (hb : d180908 q = 1) : d181058 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17744, d181058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17744, d181058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d17745 q = 1) (hb : d180908 q = 1) : d181059 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17745, d181059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17745, d181059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d17746 q = 1) (hb : d180908 q = 1) : d181060 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17746, d181060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17746, d181060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro40853 (p : Pattern) (ha : d17781 p = 1) (hb : d180908 p = 1) : d181066 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17733 q = 1) (hb : d180908 q = 1) : d181047 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17733, d181047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40850 q ha hb
    | true =>
      simp only [d17733, d181047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17734 q = 1) (hb : d180908 q = 1) : d181048 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17734, d181048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17734, d181048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17778 q = 1) (hb : d180908 q = 1) : d181063 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17778, d181063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17778, d181063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17779 q = 1) (hb : d180908 q = 1) : d181064 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17779, d181064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17779, d181064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d17780 q = 1) (hb : d180908 q = 1) : d181065 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17780, d181065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17780, d181065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d17781 q = 1) (hb : d180908 q = 1) : d181066 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17781, d181066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17781, d181066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro40854 (p : Pattern) (ha : d129332 p = 1) (hb : d180908 p = 1) : d181072 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17747 q = 1) (hb : d180908 q = 1) : d181061 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17747, d181061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40851 q ha hb
    | true =>
      simp only [d17747, d181061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40852 q ha hb
  have h2 (q : Pattern) (ha : d129328 q = 1) (hb : d180908 q = 1) : d181062 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d129328, d181062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129328, d181062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d17782 q = 1) (hb : d180908 q = 1) : d181067 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17782, d181067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40853 q ha hb
    | true =>
      simp only [d17782, d181067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17783 q = 1) (hb : d180908 q = 1) : d181068 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d17783, d181068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17783, d181068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d129329 q = 1) (hb : d180908 q = 1) : d181069 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d129329, d181069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129329, d181069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129330 q = 1) (hb : d180908 q = 1) : d181070 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d129330, d181070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129330, d181070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d129331 q = 1) (hb : d180908 q = 1) : d181071 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d129331, d181071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129331, d181071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d129332 q = 1) (hb : d180908 q = 1) : d181072 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d129332, d181072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129332, d181072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro40855 (p : Pattern) (ha : d129338 p = 1) (hb : d180908 p = 1) : d181089 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129333 q = 1) (hb : d180908 q = 1) : d181073 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d129333, d181073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129333, d181073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40854 q ha hb
  have h2 (q : Pattern) (ha : d17799 q = 1) (hb : d180908 q = 1) : d181084 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d17799, d181084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17799, d181084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40846 q ha hb
  have h3 (q : Pattern) (ha : d129334 q = 1) (hb : d180908 q = 1) : d181085 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d129334, d181085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129334, d181085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d129335 q = 1) (hb : d180908 q = 1) : d181086 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d129335, d181086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129335, d181086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d129336 q = 1) (hb : d180908 q = 1) : d181087 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d129336, d181087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129336, d181087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d129337 q = 1) (hb : d180908 q = 1) : d181088 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d129337, d181088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129337, d181088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d129338 q = 1) (hb : d180908 q = 1) : d181089 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d129338, d181089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129338, d181089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro40856 (p : Pattern) (ha : d129344 p = 1) (hb : d180908 p = 1) : d181095 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129339 q = 1) (hb : d180908 q = 1) : d181090 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d129339, d181090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129339, d181090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40855 q ha hb
  have h2 (q : Pattern) (ha : d129340 q = 1) (hb : d180908 q = 1) : d181091 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d129340, d181091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129340, d181091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d129341 q = 1) (hb : d180908 q = 1) : d181092 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d129341, d181092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129341, d181092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d129342 q = 1) (hb : d180908 q = 1) : d181093 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d129342, d181093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129342, d181093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129343 q = 1) (hb : d180908 q = 1) : d181094 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d129343, d181094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129343, d181094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129344 q = 1) (hb : d180908 q = 1) : d181095 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d129344, d181095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129344, d181095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro40857 (p : Pattern) (ha : d17835 p = 1) (hb : d180908 p = 1) : d181120 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d412 q = 1) : d412 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d319 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d413 q = 1) (hb : d131097 q = 1) : d18631 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d413, d131097, d18631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d413, d131097, d18631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d17643 q = 1) (hb : d180908 q = 1) : d180974 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17643, d180908, d180974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17643, d180908, d180974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d17644 q = 1) (hb : d180908 q = 1) : d180975 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17644, d180975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17644, d180975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1 q = 1) (hb : d971 q = 1) : d971 q = 1 := by
    exact hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d751 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d972 q = 1) (hb : d131097 q = 1) : d18843 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d972, d131097, d18843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d972, d131097, d18843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d17821 q = 1) (hb : d180908 q = 1) : d181106 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17821, d180908, d181106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d17821, d180908, d181106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h11 (q : Pattern) (ha : d17822 q = 1) (hb : d180908 q = 1) : d181107 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17822, d181107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d17822, d181107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h12 (q : Pattern) (ha : d17834 q = 1) (hb : d180908 q = 1) : d181119 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17834, d181119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17834, d181119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d17828 q = 1) (hb : d180908 q = 1) : d181113 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17828, d181113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d17828, d181113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h14 (q : Pattern) (ha : d17835 q = 1) (hb : d180908 q = 1) : d181120 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d17835, d181120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d17835, d181120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h14 p ha hb
theorem andIntro40858 (p : Pattern) (ha : d17839 p = 1) (hb : d180908 p = 1) : d181124 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d971 q = 1) : d971 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d751 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d972 q = 1) (hb : d131097 q = 1) : d18843 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d972, d131097, d18843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d972, d131097, d18843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d17821 q = 1) (hb : d180908 q = 1) : d181106 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17821, d180908, d181106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17821, d180908, d181106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d17822 q = 1) (hb : d180908 q = 1) : d181107 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17822, d181107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17822, d181107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17828 q = 1) (hb : d180908 q = 1) : d181113 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17828, d181113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17828, d181113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d17839 q = 1) (hb : d180908 q = 1) : d181124 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d17839, d181124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17839, d181124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro40859 (p : Pattern) (ha : d17858 p = 1) (hb : d180908 p = 1) : d181143 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17840 q = 1) (hb : d180908 q = 1) : d181125 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17840, d181125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40857 q ha hb
    | true =>
      simp only [d17840, d181125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40858 q ha hb
  have h2 (q : Pattern) (ha : d17841 q = 1) (hb : d180908 q = 1) : d181126 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17841, d181126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17841, d181126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17842 q = 1) (hb : d180908 q = 1) : d181127 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17842, d181127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17842, d181127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17848 q = 1) (hb : d180908 q = 1) : d181133 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17848, d181133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17848, d181133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d17857 q = 1) (hb : d180908 q = 1) : d181142 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17857, d181142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17857, d181142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d17858 q = 1) (hb : d180908 q = 1) : d181143 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d17858, d181143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17858, d181143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro40860 (p : Pattern) (ha : d17921 p = 1) (hb : d180908 p = 1) : d181166 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17859 q = 1) (hb : d180908 q = 1) : d181144 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17859, d181144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40859 q ha hb
    | true =>
      simp only [d17859, d181144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17860 q = 1) (hb : d180908 q = 1) : d181145 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17860, d181145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17860, d181145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17918 q = 1) (hb : d180908 q = 1) : d181163 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17918, d181163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17918, d181163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17919 q = 1) (hb : d180908 q = 1) : d181164 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17919, d181164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17919, d181164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d17920 q = 1) (hb : d180908 q = 1) : d181165 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17920, d181165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17920, d181165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d17921 q = 1) (hb : d180908 q = 1) : d181166 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17921, d181166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17921, d181166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro40861 (p : Pattern) (ha : d17927 p = 1) (hb : d180908 p = 1) : d181172 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17922 q = 1) (hb : d180908 q = 1) : d181167 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17922, d181167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40860 q ha hb
    | true =>
      simp only [d17922, d181167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17923 q = 1) (hb : d180908 q = 1) : d181168 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d17923, d181168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17923, d181168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17924 q = 1) (hb : d180908 q = 1) : d181169 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d17924, d181169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17924, d181169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17925 q = 1) (hb : d180908 q = 1) : d181170 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d17925, d181170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17925, d181170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17926 q = 1) (hb : d180908 q = 1) : d181171 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d17926, d181171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17926, d181171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17927 q = 1) (hb : d180908 q = 1) : d181172 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d17927, d181172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17927, d181172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro40862 (p : Pattern) (ha : d17820 p = 1) (hb : d180908 p = 1) : d181105 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d965 q = 1) : d965 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d834 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d966 q = 1) (hb : d131097 q = 1) : d18831 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d966, d131097, d18831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d966, d131097, d18831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d17812 q = 1) (hb : d180908 q = 1) : d181097 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17812, d180908, d181097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17812, d180908, d181097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d17813 q = 1) (hb : d180908 q = 1) : d181098 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17813, d181098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17813, d181098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1 q = 1) (hb : d16356 q = 1) : d16356 q = 1 := by
    exact hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d9587 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d16357 q = 1) (hb : d131097 q = 1) : d18834 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d16357, d131097, d18834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d16357, d131097, d18834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d17814 q = 1) (hb : d180908 q = 1) : d181099 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17814, d180908, d181099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d17814, d180908, d181099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h11 (q : Pattern) (ha : d17815 q = 1) (hb : d180908 q = 1) : d181100 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17815, d181100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d17815, d181100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h12 (q : Pattern) (ha : d17816 q = 1) (hb : d180908 q = 1) : d181101 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17816, d181101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17816, d181101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d1 q = 1) (hb : d14644 q = 1) : d14644 q = 1 := by
    exact hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d9597 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d14645 q = 1) (hb : d131097 q = 1) : d18838 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d14645, d131097, d18838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d14645, d131097, d18838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d17817 q = 1) (hb : d180908 q = 1) : d181102 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17817, d180908, d181102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d17817, d180908, d181102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h17 (q : Pattern) (ha : d17818 q = 1) (hb : d180908 q = 1) : d181103 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17818, d181103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d17818, d181103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h18 (q : Pattern) (ha : d1 q = 1) (hb : d12858 q = 1) : d12858 q = 1 := by
    exact hb
  have h19 (q : Pattern) (ha : d0 q = 1) (hb : d9468 q = 1) : d0 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d12859 q = 1) (hb : d131097 q = 1) : d18715 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d12859, d131097, d18715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
    | true =>
      simp only [d12859, d131097, d18715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
  have h21 (q : Pattern) (ha : d17714 q = 1) (hb : d180908 q = 1) : d181028 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17714, d180908, d181028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d17714, d180908, d181028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h22 (q : Pattern) (ha : d17715 q = 1) (hb : d180908 q = 1) : d181029 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17715, d181029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d17715, d181029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h23 (q : Pattern) (ha : d17819 q = 1) (hb : d180908 q = 1) : d181104 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17819, d181104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d17819, d181104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d17820 q = 1) (hb : d180908 q = 1) : d181105 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d17820, d181105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d17820, d181105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  exact h24 p ha hb
theorem andIntro40863 (p : Pattern) (ha : d17824 p = 1) (hb : d180908 p = 1) : d181109 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d659 q = 1) : d659 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d543 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d660 q = 1) (hb : d131097 q = 1) : d18708 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d660, d131097, d18708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d660, d131097, d18708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d17709 q = 1) (hb : d180908 q = 1) : d181023 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17709, d180908, d181023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17709, d180908, d181023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d17710 q = 1) (hb : d180908 q = 1) : d181024 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17710, d181024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17710, d181024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1 q = 1) (hb : d16156 q = 1) : d16156 q = 1 := by
    exact hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d9458 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d16157 q = 1) (hb : d131097 q = 1) : d18711 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d16157, d131097, d18711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d16157, d131097, d18711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d17711 q = 1) (hb : d180908 q = 1) : d181025 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17711, d180908, d181025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d17711, d180908, d181025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h11 (q : Pattern) (ha : d17712 q = 1) (hb : d180908 q = 1) : d181026 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17712, d181026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d17712, d181026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h12 (q : Pattern) (ha : d17713 q = 1) (hb : d180908 q = 1) : d181027 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17713, d181027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17713, d181027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d1 q = 1) (hb : d12858 q = 1) : d12858 q = 1 := by
    exact hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d9468 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d12859 q = 1) (hb : d131097 q = 1) : d18715 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d12859, d131097, d18715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d12859, d131097, d18715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d17714 q = 1) (hb : d180908 q = 1) : d181028 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17714, d180908, d181028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d17714, d180908, d181028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h17 (q : Pattern) (ha : d17715 q = 1) (hb : d180908 q = 1) : d181029 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17715, d181029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d17715, d181029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h18 (q : Pattern) (ha : d1 q = 1) (hb : d971 q = 1) : d971 q = 1 := by
    exact hb
  have h19 (q : Pattern) (ha : d0 q = 1) (hb : d751 q = 1) : d0 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d972 q = 1) (hb : d131097 q = 1) : d18843 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d972, d131097, d18843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
    | true =>
      simp only [d972, d131097, d18843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
  have h21 (q : Pattern) (ha : d17821 q = 1) (hb : d180908 q = 1) : d181106 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17821, d180908, d181106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d17821, d180908, d181106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h22 (q : Pattern) (ha : d17822 q = 1) (hb : d180908 q = 1) : d181107 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17822, d181107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d17822, d181107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h23 (q : Pattern) (ha : d17823 q = 1) (hb : d180908 q = 1) : d181108 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17823, d181108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d17823, d181108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d17824 q = 1) (hb : d180908 q = 1) : d181109 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d17824, d181109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d17824, d181109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  exact h24 p ha hb
theorem andIntro40864 (p : Pattern) (ha : d17829 p = 1) (hb : d180908 p = 1) : d181114 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d12858 q = 1) : d12858 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d9468 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12859 q = 1) (hb : d131097 q = 1) : d18715 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d12859, d131097, d18715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d12859, d131097, d18715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d17714 q = 1) (hb : d180908 q = 1) : d181028 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17714, d180908, d181028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17714, d180908, d181028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d17715 q = 1) (hb : d180908 q = 1) : d181029 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17715, d181029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17715, d181029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1 q = 1) (hb : d971 q = 1) : d971 q = 1 := by
    exact hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d751 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d972 q = 1) (hb : d131097 q = 1) : d18843 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d972, d131097, d18843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d972, d131097, d18843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d17821 q = 1) (hb : d180908 q = 1) : d181106 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17821, d180908, d181106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d17821, d180908, d181106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h11 (q : Pattern) (ha : d17822 q = 1) (hb : d180908 q = 1) : d181107 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17822, d181107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d17822, d181107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h12 (q : Pattern) (ha : d17823 q = 1) (hb : d180908 q = 1) : d181108 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17823, d181108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17823, d181108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d17828 q = 1) (hb : d180908 q = 1) : d181113 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17828, d181113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d17828, d181113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h14 (q : Pattern) (ha : d17829 q = 1) (hb : d180908 q = 1) : d181114 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d17829, d181114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d17829, d181114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h14 p ha hb
theorem andIntro40865 (p : Pattern) (ha : d17845 p = 1) (hb : d180908 p = 1) : d181130 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17825 q = 1) (hb : d180908 q = 1) : d181110 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17825, d181110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40862 q ha hb
    | true =>
      simp only [d17825, d181110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40863 q ha hb
  have h2 (q : Pattern) (ha : d17826 q = 1) (hb : d180908 q = 1) : d181111 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17826, d181111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17826, d181111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17827 q = 1) (hb : d180908 q = 1) : d181112 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17827, d181112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17827, d181112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17830 q = 1) (hb : d180908 q = 1) : d181115 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17830, d181115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40863 q ha hb
    | true =>
      simp only [d17830, d181115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40864 q ha hb
  have h5 (q : Pattern) (ha : d17831 q = 1) (hb : d180908 q = 1) : d181116 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17831, d181116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17831, d181116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17832 q = 1) (hb : d180908 q = 1) : d181117 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17832, d181117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17832, d181117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17833 q = 1) (hb : d180908 q = 1) : d181118 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17833, d181118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17833, d181118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17836 q = 1) (hb : d180908 q = 1) : d181121 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17836, d181121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40863 q ha hb
    | true =>
      simp only [d17836, d181121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40857 q ha hb
  have h9 (q : Pattern) (ha : d17837 q = 1) (hb : d180908 q = 1) : d181122 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17837, d181122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17837, d181122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d17838 q = 1) (hb : d180908 q = 1) : d181123 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17838, d181123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17838, d181123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d17840 q = 1) (hb : d180908 q = 1) : d181125 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17840, d181125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40857 q ha hb
    | true =>
      simp only [d17840, d181125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40858 q ha hb
  have h12 (q : Pattern) (ha : d17841 q = 1) (hb : d180908 q = 1) : d181126 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17841, d181126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17841, d181126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d17842 q = 1) (hb : d180908 q = 1) : d181127 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17842, d181127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17842, d181127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d17843 q = 1) (hb : d180908 q = 1) : d181128 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17843, d181128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d17843, d181128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d17844 q = 1) (hb : d180908 q = 1) : d181129 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17844, d181129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17844, d181129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d17845 q = 1) (hb : d180908 q = 1) : d181130 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d17845, d181130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d17845, d181130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro40866 (p : Pattern) (ha : d17850 p = 1) (hb : d180908 p = 1) : d181135 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17836 q = 1) (hb : d180908 q = 1) : d181121 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17836, d181121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40863 q ha hb
    | true =>
      simp only [d17836, d181121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40857 q ha hb
  have h2 (q : Pattern) (ha : d17837 q = 1) (hb : d180908 q = 1) : d181122 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17837, d181122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17837, d181122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17838 q = 1) (hb : d180908 q = 1) : d181123 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17838, d181123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17838, d181123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17840 q = 1) (hb : d180908 q = 1) : d181125 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17840, d181125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40857 q ha hb
    | true =>
      simp only [d17840, d181125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40858 q ha hb
  have h5 (q : Pattern) (ha : d17841 q = 1) (hb : d180908 q = 1) : d181126 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17841, d181126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17841, d181126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17842 q = 1) (hb : d180908 q = 1) : d181127 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17842, d181127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17842, d181127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17843 q = 1) (hb : d180908 q = 1) : d181128 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17843, d181128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17843, d181128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17848 q = 1) (hb : d180908 q = 1) : d181133 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17848, d181133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17848, d181133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d17849 q = 1) (hb : d180908 q = 1) : d181134 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17849, d181134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17849, d181134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d17850 q = 1) (hb : d180908 q = 1) : d181135 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d17850, d181135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d17850, d181135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro40867 (p : Pattern) (ha : d17856 p = 1) (hb : d180908 p = 1) : d181141 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17846 q = 1) (hb : d180908 q = 1) : d181131 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17846, d181131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40865 q ha hb
    | true =>
      simp only [d17846, d181131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17847 q = 1) (hb : d180908 q = 1) : d181132 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17847, d181132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17847, d181132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17851 q = 1) (hb : d180908 q = 1) : d181136 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17851, d181136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40866 q ha hb
    | true =>
      simp only [d17851, d181136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17852 q = 1) (hb : d180908 q = 1) : d181137 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17852, d181137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17852, d181137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17853 q = 1) (hb : d180908 q = 1) : d181138 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17853, d181138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17853, d181138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17854 q = 1) (hb : d180908 q = 1) : d181139 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17854, d181139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17854, d181139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d17855 q = 1) (hb : d180908 q = 1) : d181140 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17855, d181140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17855, d181140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d17856 q = 1) (hb : d180908 q = 1) : d181141 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17856, d181141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17856, d181141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro40868 (p : Pattern) (ha : d17864 p = 1) (hb : d180908 p = 1) : d181149 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17851 q = 1) (hb : d180908 q = 1) : d181136 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17851, d181136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40866 q ha hb
    | true =>
      simp only [d17851, d181136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17852 q = 1) (hb : d180908 q = 1) : d181137 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17852, d181137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17852, d181137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17859 q = 1) (hb : d180908 q = 1) : d181144 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17859, d181144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40859 q ha hb
    | true =>
      simp only [d17859, d181144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17860 q = 1) (hb : d180908 q = 1) : d181145 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17860, d181145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17860, d181145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17861 q = 1) (hb : d180908 q = 1) : d181146 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17861, d181146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17861, d181146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17862 q = 1) (hb : d180908 q = 1) : d181147 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17862, d181147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17862, d181147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d17863 q = 1) (hb : d180908 q = 1) : d181148 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17863, d181148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17863, d181148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d17864 q = 1) (hb : d180908 q = 1) : d181149 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17864, d181149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17864, d181149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro40869 (p : Pattern) (ha : d17910 p = 1) (hb : d180908 p = 1) : d181155 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17851 q = 1) (hb : d180908 q = 1) : d181136 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17851, d181136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40866 q ha hb
    | true =>
      simp only [d17851, d181136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17852 q = 1) (hb : d180908 q = 1) : d181137 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17852, d181137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17852, d181137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17907 q = 1) (hb : d180908 q = 1) : d181152 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17907, d181152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17907, d181152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17908 q = 1) (hb : d180908 q = 1) : d181153 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17908, d181153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17908, d181153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d17909 q = 1) (hb : d180908 q = 1) : d181154 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17909, d181154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17909, d181154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d17910 q = 1) (hb : d180908 q = 1) : d181155 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17910, d181155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17910, d181155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro40870 (p : Pattern) (ha : d129350 p = 1) (hb : d180908 p = 1) : d181161 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17865 q = 1) (hb : d180908 q = 1) : d181150 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17865, d181150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40867 q ha hb
    | true =>
      simp only [d17865, d181150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40868 q ha hb
  have h2 (q : Pattern) (ha : d129346 q = 1) (hb : d180908 q = 1) : d181151 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d129346, d181151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129346, d181151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d17911 q = 1) (hb : d180908 q = 1) : d181156 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17911, d181156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40869 q ha hb
    | true =>
      simp only [d17911, d181156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17912 q = 1) (hb : d180908 q = 1) : d181157 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d17912, d181157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17912, d181157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d129347 q = 1) (hb : d180908 q = 1) : d181158 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d129347, d181158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129347, d181158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129348 q = 1) (hb : d180908 q = 1) : d181159 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d129348, d181159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129348, d181159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d129349 q = 1) (hb : d180908 q = 1) : d181160 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d129349, d181160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129349, d181160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d129350 q = 1) (hb : d180908 q = 1) : d181161 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d129350, d181161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129350, d181161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro40871 (p : Pattern) (ha : d129356 p = 1) (hb : d180908 p = 1) : d181178 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129351 q = 1) (hb : d180908 q = 1) : d181162 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d129351, d181162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129351, d181162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40870 q ha hb
  have h2 (q : Pattern) (ha : d17928 q = 1) (hb : d180908 q = 1) : d181173 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d17928, d181173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17928, d181173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40861 q ha hb
  have h3 (q : Pattern) (ha : d129352 q = 1) (hb : d180908 q = 1) : d181174 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d129352, d181174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129352, d181174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d129353 q = 1) (hb : d180908 q = 1) : d181175 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d129353, d181175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129353, d181175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d129354 q = 1) (hb : d180908 q = 1) : d181176 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d129354, d181176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129354, d181176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d129355 q = 1) (hb : d180908 q = 1) : d181177 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d129355, d181177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129355, d181177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d129356 q = 1) (hb : d180908 q = 1) : d181178 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d129356, d181178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129356, d181178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro40872 (p : Pattern) (ha : d129362 p = 1) (hb : d180908 p = 1) : d181184 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129357 q = 1) (hb : d180908 q = 1) : d181179 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d129357, d181179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129357, d181179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40871 q ha hb
  have h2 (q : Pattern) (ha : d129358 q = 1) (hb : d180908 q = 1) : d181180 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d129358, d181180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129358, d181180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d129359 q = 1) (hb : d180908 q = 1) : d181181 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d129359, d181181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129359, d181181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d129360 q = 1) (hb : d180908 q = 1) : d181182 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d129360, d181182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129360, d181182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129361 q = 1) (hb : d180908 q = 1) : d181183 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d129361, d181183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129361, d181183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129362 q = 1) (hb : d180908 q = 1) : d181184 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d129362, d181184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129362, d181184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro40873 (p : Pattern) (ha : d17979 p = 1) (hb : d180908 p = 1) : d181224 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1385 q = 1) : d1385 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1110 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1386 q = 1) (hb : d131097 q = 1) : d19031 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1386, d131097, d19031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1386, d131097, d19031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d17974 q = 1) (hb : d180908 q = 1) : d181219 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17974, d180908, d181219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17974, d180908, d181219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d17975 q = 1) (hb : d180908 q = 1) : d181220 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17975, d181220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17975, d181220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1 q = 1) (hb : d1391 q = 1) : d1391 q = 1 := by
    exact hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d1121 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d1392 q = 1) (hb : d131097 q = 1) : d19034 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1392, d131097, d19034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d1392, d131097, d19034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d17976 q = 1) (hb : d180908 q = 1) : d181221 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17976, d180908, d181221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d17976, d180908, d181221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h11 (q : Pattern) (ha : d17977 q = 1) (hb : d180908 q = 1) : d181222 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17977, d181222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d17977, d181222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h12 (q : Pattern) (ha : d17978 q = 1) (hb : d180908 q = 1) : d181223 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17978, d181223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17978, d181223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d1 q = 1) (hb : d15004 q = 1) : d15004 q = 1 := by
    exact hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d9800 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d15005 q = 1) (hb : d131097 q = 1) : d19013 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15005, d131097, d19013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d15005, d131097, d19013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d17958 q = 1) (hb : d180908 q = 1) : d181203 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17958, d180908, d181203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d17958, d180908, d181203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h17 (q : Pattern) (ha : d17959 q = 1) (hb : d180908 q = 1) : d181204 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17959, d181204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d17959, d181204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h18 (q : Pattern) (ha : d17968 q = 1) (hb : d180908 q = 1) : d181213 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17968, d181213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d17968, d181213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h19 (q : Pattern) (ha : d17979 q = 1) (hb : d180908 q = 1) : d181224 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d17979, d181224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d17979, d181224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro40874 (p : Pattern) (ha : d18008 p = 1) (hb : d180908 p = 1) : d181253 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1391 q = 1) : d1391 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1121 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1392 q = 1) (hb : d131097 q = 1) : d19034 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1392, d131097, d19034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1392, d131097, d19034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d17976 q = 1) (hb : d180908 q = 1) : d181221 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17976, d180908, d181221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17976, d180908, d181221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d17977 q = 1) (hb : d180908 q = 1) : d181222 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17977, d181222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17977, d181222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d18007 q = 1) (hb : d180908 q = 1) : d181252 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18007, d181252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d18007, d181252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d1 q = 1) (hb : d15019 q = 1) : d15019 q = 1 := by
    exact hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d9844 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d15020 q = 1) (hb : d131097 q = 1) : d19046 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15020, d131097, d19046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d15020, d131097, d19046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d17986 q = 1) (hb : d180908 q = 1) : d181231 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17986, d180908, d181231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d17986, d180908, d181231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h12 (q : Pattern) (ha : d17987 q = 1) (hb : d180908 q = 1) : d181232 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17987, d181232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d17987, d181232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h13 (q : Pattern) (ha : d17988 q = 1) (hb : d180908 q = 1) : d181233 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17988, d181233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d17988, d181233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h14 (q : Pattern) (ha : d18008 q = 1) (hb : d180908 q = 1) : d181253 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d18008, d181253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d18008, d181253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h14 p ha hb
theorem andIntro40875 (p : Pattern) (ha : d18014 p = 1) (hb : d180908 p = 1) : d181259 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18009 q = 1) (hb : d180908 q = 1) : d181254 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18009, d181254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40873 q ha hb
    | true =>
      simp only [d18009, d181254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40874 q ha hb
  have h2 (q : Pattern) (ha : d18010 q = 1) (hb : d180908 q = 1) : d181255 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18010, d181255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18010, d181255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18011 q = 1) (hb : d180908 q = 1) : d181256 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18011, d181256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18011, d181256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d18012 q = 1) (hb : d180908 q = 1) : d181257 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18012, d181257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18012, d181257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d18013 q = 1) (hb : d180908 q = 1) : d181258 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d18013, d181258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18013, d181258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d18014 q = 1) (hb : d180908 q = 1) : d181259 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d18014, d181259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d18014, d181259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro40876 (p : Pattern) (ha : d18101 p = 1) (hb : d180908 p = 1) : d181291 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18015 q = 1) (hb : d180908 q = 1) : d181260 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18015, d181260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40875 q ha hb
    | true =>
      simp only [d18015, d181260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d18016 q = 1) (hb : d180908 q = 1) : d181261 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18016, d181261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18016, d181261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18098 q = 1) (hb : d180908 q = 1) : d181288 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d18098, d181288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18098, d181288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18099 q = 1) (hb : d180908 q = 1) : d181289 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d18099, d181289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18099, d181289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d18100 q = 1) (hb : d180908 q = 1) : d181290 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d18100, d181290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18100, d181290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d18101 q = 1) (hb : d180908 q = 1) : d181291 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d18101, d181291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d18101, d181291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro40877 (p : Pattern) (ha : d18107 p = 1) (hb : d180908 p = 1) : d181297 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18102 q = 1) (hb : d180908 q = 1) : d181292 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d18102, d181292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40876 q ha hb
    | true =>
      simp only [d18102, d181292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d18103 q = 1) (hb : d180908 q = 1) : d181293 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d18103, d181293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18103, d181293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18104 q = 1) (hb : d180908 q = 1) : d181294 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d18104, d181294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18104, d181294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18105 q = 1) (hb : d180908 q = 1) : d181295 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d18105, d181295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18105, d181295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d18106 q = 1) (hb : d180908 q = 1) : d181296 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d18106, d181296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18106, d181296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d18107 q = 1) (hb : d180908 q = 1) : d181297 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d18107, d181297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18107, d181297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro40878 (p : Pattern) (ha : d17952 p = 1) (hb : d180908 p = 1) : d181197 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1376 q = 1) : d1376 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1210 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1377 q = 1) (hb : d131097 q = 1) : d18991 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1377, d131097, d18991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1377, d131097, d18991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d17942 q = 1) (hb : d180908 q = 1) : d181187 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17942, d180908, d181187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17942, d180908, d181187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d17943 q = 1) (hb : d180908 q = 1) : d181188 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17943, d181188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17943, d181188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1 q = 1) (hb : d16649 q = 1) : d16649 q = 1 := by
    exact hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d9753 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d16650 q = 1) (hb : d131097 q = 1) : d18994 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d16650, d131097, d18994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d16650, d131097, d18994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d17944 q = 1) (hb : d180908 q = 1) : d181189 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17944, d180908, d181189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d17944, d180908, d181189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h11 (q : Pattern) (ha : d17945 q = 1) (hb : d180908 q = 1) : d181190 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17945, d181190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d17945, d181190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h12 (q : Pattern) (ha : d17946 q = 1) (hb : d180908 q = 1) : d181191 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17946, d181191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17946, d181191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d1 q = 1) (hb : d14987 q = 1) : d14987 q = 1 := by
    exact hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d9763 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d14988 q = 1) (hb : d131097 q = 1) : d18998 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d14988, d131097, d18998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d14988, d131097, d18998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d17947 q = 1) (hb : d180908 q = 1) : d181192 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17947, d180908, d181192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d17947, d180908, d181192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h17 (q : Pattern) (ha : d17948 q = 1) (hb : d180908 q = 1) : d181193 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17948, d181193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d17948, d181193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h18 (q : Pattern) (ha : d1 q = 1) (hb : d14994 q = 1) : d14994 q = 1 := by
    exact hb
  have h19 (q : Pattern) (ha : d0 q = 1) (hb : d9778 q = 1) : d0 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d14995 q = 1) (hb : d131097 q = 1) : d19001 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d14995, d131097, d19001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
    | true =>
      simp only [d14995, d131097, d19001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
  have h21 (q : Pattern) (ha : d17949 q = 1) (hb : d180908 q = 1) : d181194 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17949, d180908, d181194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d17949, d180908, d181194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h22 (q : Pattern) (ha : d17950 q = 1) (hb : d180908 q = 1) : d181195 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17950, d181195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d17950, d181195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h23 (q : Pattern) (ha : d17951 q = 1) (hb : d180908 q = 1) : d181196 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17951, d181196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d17951, d181196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d17952 q = 1) (hb : d180908 q = 1) : d181197 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d17952, d181197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d17952, d181197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  exact h24 p ha hb
theorem andIntro40879 (p : Pattern) (ha : d17961 p = 1) (hb : d180908 p = 1) : d181206 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1380 q = 1) : d1380 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1100 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1381 q = 1) (hb : d131097 q = 1) : d19006 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1381, d131097, d19006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1381, d131097, d19006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d17953 q = 1) (hb : d180908 q = 1) : d181198 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17953, d180908, d181198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17953, d180908, d181198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d17954 q = 1) (hb : d180908 q = 1) : d181199 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17954, d181199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17954, d181199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1 q = 1) (hb : d16656 q = 1) : d16656 q = 1 := by
    exact hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d9789 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d16657 q = 1) (hb : d131097 q = 1) : d19009 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d16657, d131097, d19009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d16657, d131097, d19009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d17955 q = 1) (hb : d180908 q = 1) : d181200 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17955, d180908, d181200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d17955, d180908, d181200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h11 (q : Pattern) (ha : d17956 q = 1) (hb : d180908 q = 1) : d181201 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17956, d181201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d17956, d181201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h12 (q : Pattern) (ha : d17957 q = 1) (hb : d180908 q = 1) : d181202 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17957, d181202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17957, d181202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d1 q = 1) (hb : d14994 q = 1) : d14994 q = 1 := by
    exact hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d9778 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d14995 q = 1) (hb : d131097 q = 1) : d19001 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d14995, d131097, d19001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d14995, d131097, d19001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d17949 q = 1) (hb : d180908 q = 1) : d181194 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17949, d180908, d181194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d17949, d180908, d181194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h17 (q : Pattern) (ha : d17950 q = 1) (hb : d180908 q = 1) : d181195 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17950, d181195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d17950, d181195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h18 (q : Pattern) (ha : d1 q = 1) (hb : d15004 q = 1) : d15004 q = 1 := by
    exact hb
  have h19 (q : Pattern) (ha : d0 q = 1) (hb : d9800 q = 1) : d0 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d15005 q = 1) (hb : d131097 q = 1) : d19013 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15005, d131097, d19013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
    | true =>
      simp only [d15005, d131097, d19013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
  have h21 (q : Pattern) (ha : d17958 q = 1) (hb : d180908 q = 1) : d181203 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17958, d180908, d181203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d17958, d180908, d181203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h22 (q : Pattern) (ha : d17959 q = 1) (hb : d180908 q = 1) : d181204 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17959, d181204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d17959, d181204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h23 (q : Pattern) (ha : d17960 q = 1) (hb : d180908 q = 1) : d181205 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17960, d181205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d17960, d181205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d17961 q = 1) (hb : d180908 q = 1) : d181206 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d17961, d181206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d17961, d181206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  exact h24 p ha hb
theorem andIntro40880 (p : Pattern) (ha : d17969 p = 1) (hb : d180908 p = 1) : d181214 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d13160 q = 1) : d13160 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d9814 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d13161 q = 1) (hb : d131097 q = 1) : d19021 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13161, d131097, d19021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d13161, d131097, d19021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d17965 q = 1) (hb : d180908 q = 1) : d181210 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17965, d180908, d181210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17965, d180908, d181210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d17966 q = 1) (hb : d180908 q = 1) : d181211 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17966, d181211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17966, d181211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1 q = 1) (hb : d15004 q = 1) : d15004 q = 1 := by
    exact hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d9800 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d15005 q = 1) (hb : d131097 q = 1) : d19013 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15005, d131097, d19013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d15005, d131097, d19013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d17958 q = 1) (hb : d180908 q = 1) : d181203 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17958, d180908, d181203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d17958, d180908, d181203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h11 (q : Pattern) (ha : d17959 q = 1) (hb : d180908 q = 1) : d181204 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17959, d181204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d17959, d181204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h12 (q : Pattern) (ha : d17967 q = 1) (hb : d180908 q = 1) : d181212 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17967, d181212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17967, d181212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d17968 q = 1) (hb : d180908 q = 1) : d181213 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17968, d181213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d17968, d181213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h14 (q : Pattern) (ha : d17969 q = 1) (hb : d180908 q = 1) : d181214 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d17969, d181214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d17969, d181214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h14 p ha hb
theorem andIntro40881 (p : Pattern) (ha : d17989 p = 1) (hb : d180908 p = 1) : d181234 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d6350 q = 1) : d6350 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d5018 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d6351 q = 1) (hb : d131097 q = 1) : d19042 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d6351, d131097, d19042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d6351, d131097, d19042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d17983 q = 1) (hb : d180908 q = 1) : d181228 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17983, d180908, d181228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17983, d180908, d181228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d17984 q = 1) (hb : d180908 q = 1) : d181229 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17984, d181229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17984, d181229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17985 q = 1) (hb : d180908 q = 1) : d181230 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17985, d181230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17985, d181230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d1 q = 1) (hb : d15019 q = 1) : d15019 q = 1 := by
    exact hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d9844 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d15020 q = 1) (hb : d131097 q = 1) : d19046 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15020, d131097, d19046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d15020, d131097, d19046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d17986 q = 1) (hb : d180908 q = 1) : d181231 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17986, d180908, d181231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d17986, d180908, d181231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h12 (q : Pattern) (ha : d17987 q = 1) (hb : d180908 q = 1) : d181232 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17987, d181232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d17987, d181232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h13 (q : Pattern) (ha : d17988 q = 1) (hb : d180908 q = 1) : d181233 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17988, d181233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d17988, d181233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h14 (q : Pattern) (ha : d17989 q = 1) (hb : d180908 q = 1) : d181234 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d17989, d181234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17989, d181234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h14 p ha hb
theorem andIntro40882 (p : Pattern) (ha : d17995 p = 1) (hb : d180908 p = 1) : d181240 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17962 q = 1) (hb : d180908 q = 1) : d181207 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17962, d181207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40878 q ha hb
    | true =>
      simp only [d17962, d181207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40879 q ha hb
  have h2 (q : Pattern) (ha : d17963 q = 1) (hb : d180908 q = 1) : d181208 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17963, d181208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17963, d181208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17964 q = 1) (hb : d180908 q = 1) : d181209 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17964, d181209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17964, d181209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17970 q = 1) (hb : d180908 q = 1) : d181215 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17970, d181215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40879 q ha hb
    | true =>
      simp only [d17970, d181215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40880 q ha hb
  have h5 (q : Pattern) (ha : d17971 q = 1) (hb : d180908 q = 1) : d181216 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17971, d181216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17971, d181216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17972 q = 1) (hb : d180908 q = 1) : d181217 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17972, d181217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17972, d181217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17973 q = 1) (hb : d180908 q = 1) : d181218 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17973, d181218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17973, d181218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17980 q = 1) (hb : d180908 q = 1) : d181225 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17980, d181225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40879 q ha hb
    | true =>
      simp only [d17980, d181225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40873 q ha hb
  have h9 (q : Pattern) (ha : d17981 q = 1) (hb : d180908 q = 1) : d181226 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17981, d181226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17981, d181226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d17982 q = 1) (hb : d180908 q = 1) : d181227 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17982, d181227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17982, d181227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d17990 q = 1) (hb : d180908 q = 1) : d181235 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17990, d181235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40873 q ha hb
    | true =>
      simp only [d17990, d181235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40881 q ha hb
  have h12 (q : Pattern) (ha : d17991 q = 1) (hb : d180908 q = 1) : d181236 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17991, d181236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17991, d181236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d17992 q = 1) (hb : d180908 q = 1) : d181237 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17992, d181237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17992, d181237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d17993 q = 1) (hb : d180908 q = 1) : d181238 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17993, d181238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d17993, d181238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d17994 q = 1) (hb : d180908 q = 1) : d181239 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17994, d181239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17994, d181239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d17995 q = 1) (hb : d180908 q = 1) : d181240 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d17995, d181240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d17995, d181240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro40883 (p : Pattern) (ha : d18000 p = 1) (hb : d180908 p = 1) : d181245 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17980 q = 1) (hb : d180908 q = 1) : d181225 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17980, d181225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40879 q ha hb
    | true =>
      simp only [d17980, d181225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40873 q ha hb
  have h2 (q : Pattern) (ha : d17981 q = 1) (hb : d180908 q = 1) : d181226 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17981, d181226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17981, d181226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17982 q = 1) (hb : d180908 q = 1) : d181227 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17982, d181227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17982, d181227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17990 q = 1) (hb : d180908 q = 1) : d181235 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17990, d181235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40873 q ha hb
    | true =>
      simp only [d17990, d181235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40881 q ha hb
  have h5 (q : Pattern) (ha : d17991 q = 1) (hb : d180908 q = 1) : d181236 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17991, d181236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17991, d181236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17992 q = 1) (hb : d180908 q = 1) : d181237 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17992, d181237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17992, d181237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17993 q = 1) (hb : d180908 q = 1) : d181238 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17993, d181238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17993, d181238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17998 q = 1) (hb : d180908 q = 1) : d181243 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17998, d181243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17998, d181243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d17999 q = 1) (hb : d180908 q = 1) : d181244 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17999, d181244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17999, d181244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d18000 q = 1) (hb : d180908 q = 1) : d181245 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d18000, d181245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d18000, d181245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro40884 (p : Pattern) (ha : d18006 p = 1) (hb : d180908 p = 1) : d181251 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17996 q = 1) (hb : d180908 q = 1) : d181241 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17996, d181241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40882 q ha hb
    | true =>
      simp only [d17996, d181241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17997 q = 1) (hb : d180908 q = 1) : d181242 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17997, d181242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17997, d181242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18001 q = 1) (hb : d180908 q = 1) : d181246 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18001, d181246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40883 q ha hb
    | true =>
      simp only [d18001, d181246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18002 q = 1) (hb : d180908 q = 1) : d181247 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18002, d181247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18002, d181247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d18003 q = 1) (hb : d180908 q = 1) : d181248 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d18003, d181248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18003, d181248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d18004 q = 1) (hb : d180908 q = 1) : d181249 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d18004, d181249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d18004, d181249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d18005 q = 1) (hb : d180908 q = 1) : d181250 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d18005, d181250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d18005, d181250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d18006 q = 1) (hb : d180908 q = 1) : d181251 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d18006, d181251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d18006, d181251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro40885 (p : Pattern) (ha : d18020 p = 1) (hb : d180908 p = 1) : d181265 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18001 q = 1) (hb : d180908 q = 1) : d181246 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18001, d181246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40883 q ha hb
    | true =>
      simp only [d18001, d181246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d18002 q = 1) (hb : d180908 q = 1) : d181247 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18002, d181247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18002, d181247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18015 q = 1) (hb : d180908 q = 1) : d181260 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18015, d181260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40875 q ha hb
    | true =>
      simp only [d18015, d181260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18016 q = 1) (hb : d180908 q = 1) : d181261 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18016, d181261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18016, d181261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d18017 q = 1) (hb : d180908 q = 1) : d181262 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d18017, d181262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18017, d181262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d18018 q = 1) (hb : d180908 q = 1) : d181263 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d18018, d181263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d18018, d181263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d18019 q = 1) (hb : d180908 q = 1) : d181264 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d18019, d181264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d18019, d181264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d18020 q = 1) (hb : d180908 q = 1) : d181265 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d18020, d181265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d18020, d181265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro40886 (p : Pattern) (ha : d18078 p = 1) (hb : d180908 p = 1) : d181268 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1391 q = 1) : d1391 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1121 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1392 q = 1) (hb : d131097 q = 1) : d19034 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1392, d131097, d19034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1392, d131097, d19034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d17976 q = 1) (hb : d180908 q = 1) : d181221 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17976, d180908, d181221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17976, d180908, d181221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d17977 q = 1) (hb : d180908 q = 1) : d181222 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17977, d181222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17977, d181222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d18007 q = 1) (hb : d180908 q = 1) : d181252 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18007, d181252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d18007, d181252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d18078 q = 1) (hb : d180908 q = 1) : d181268 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d18078, d181268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d18078, d181268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro40887 (p : Pattern) (ha : d18084 p = 1) (hb : d180908 p = 1) : d181274 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17980 q = 1) (hb : d180908 q = 1) : d181225 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17980, d181225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40879 q ha hb
    | true =>
      simp only [d17980, d181225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40873 q ha hb
  have h2 (q : Pattern) (ha : d17981 q = 1) (hb : d180908 q = 1) : d181226 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17981, d181226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17981, d181226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17982 q = 1) (hb : d180908 q = 1) : d181227 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17982, d181227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17982, d181227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17990 q = 1) (hb : d180908 q = 1) : d181235 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17990, d181235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40873 q ha hb
    | true =>
      simp only [d17990, d181235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40881 q ha hb
  have h5 (q : Pattern) (ha : d17991 q = 1) (hb : d180908 q = 1) : d181236 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17991, d181236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17991, d181236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17992 q = 1) (hb : d180908 q = 1) : d181237 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17992, d181237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17992, d181237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17993 q = 1) (hb : d180908 q = 1) : d181238 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17993, d181238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17993, d181238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d18079 q = 1) (hb : d180908 q = 1) : d181269 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18079, d181269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40873 q ha hb
    | true =>
      simp only [d18079, d181269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40886 q ha hb
  have h9 (q : Pattern) (ha : d18080 q = 1) (hb : d180908 q = 1) : d181270 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18080, d181270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18080, d181270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d18081 q = 1) (hb : d180908 q = 1) : d181271 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18081, d181271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18081, d181271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d18082 q = 1) (hb : d180908 q = 1) : d181272 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18082, d181272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d18082, d181272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d18083 q = 1) (hb : d180908 q = 1) : d181273 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d18083, d181273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d18083, d181273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d18084 q = 1) (hb : d180908 q = 1) : d181274 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d18084, d181274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d18084, d181274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro40888 (p : Pattern) (ha : d18090 p = 1) (hb : d180908 p = 1) : d181280 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18085 q = 1) (hb : d180908 q = 1) : d181275 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18085, d181275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40887 q ha hb
    | true =>
      simp only [d18085, d181275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d18086 q = 1) (hb : d180908 q = 1) : d181276 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18086, d181276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18086, d181276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18087 q = 1) (hb : d180908 q = 1) : d181277 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d18087, d181277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18087, d181277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18088 q = 1) (hb : d180908 q = 1) : d181278 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d18088, d181278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18088, d181278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d18089 q = 1) (hb : d180908 q = 1) : d181279 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d18089, d181279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18089, d181279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d18090 q = 1) (hb : d180908 q = 1) : d181280 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d18090, d181280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d18090, d181280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro40889 (p : Pattern) (ha : d129369 p = 1) (hb : d180908 p = 1) : d181286 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18021 q = 1) (hb : d180908 q = 1) : d181266 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d18021, d181266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40884 q ha hb
    | true =>
      simp only [d18021, d181266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40885 q ha hb
  have h2 (q : Pattern) (ha : d129365 q = 1) (hb : d180908 q = 1) : d181267 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d129365, d181267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129365, d181267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d18091 q = 1) (hb : d180908 q = 1) : d181281 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d18091, d181281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40888 q ha hb
    | true =>
      simp only [d18091, d181281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18092 q = 1) (hb : d180908 q = 1) : d181282 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d18092, d181282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18092, d181282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d129366 q = 1) (hb : d180908 q = 1) : d181283 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d129366, d181283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129366, d181283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129367 q = 1) (hb : d180908 q = 1) : d181284 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d129367, d181284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129367, d181284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d129368 q = 1) (hb : d180908 q = 1) : d181285 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d129368, d181285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129368, d181285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d129369 q = 1) (hb : d180908 q = 1) : d181286 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d129369, d181286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129369, d181286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro40890 (p : Pattern) (ha : d129375 p = 1) (hb : d180908 p = 1) : d181303 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129370 q = 1) (hb : d180908 q = 1) : d181287 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d129370, d181287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129370, d181287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40889 q ha hb
  have h2 (q : Pattern) (ha : d18108 q = 1) (hb : d180908 q = 1) : d181298 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d18108, d181298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18108, d181298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40877 q ha hb
  have h3 (q : Pattern) (ha : d129371 q = 1) (hb : d180908 q = 1) : d181299 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d129371, d181299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129371, d181299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d129372 q = 1) (hb : d180908 q = 1) : d181300 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d129372, d181300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129372, d181300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d129373 q = 1) (hb : d180908 q = 1) : d181301 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d129373, d181301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129373, d181301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d129374 q = 1) (hb : d180908 q = 1) : d181302 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d129374, d181302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129374, d181302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d129375 q = 1) (hb : d180908 q = 1) : d181303 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d129375, d181303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129375, d181303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro40891 (p : Pattern) (ha : d129381 p = 1) (hb : d180908 p = 1) : d181309 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129376 q = 1) (hb : d180908 q = 1) : d181304 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d129376, d181304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129376, d181304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40890 q ha hb
  have h2 (q : Pattern) (ha : d129377 q = 1) (hb : d180908 q = 1) : d181305 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d129377, d181305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129377, d181305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d129378 q = 1) (hb : d180908 q = 1) : d181306 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d129378, d181306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129378, d181306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d129379 q = 1) (hb : d180908 q = 1) : d181307 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d129379, d181307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129379, d181307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129380 q = 1) (hb : d180908 q = 1) : d181308 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d129380, d181308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129380, d181308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129381 q = 1) (hb : d180908 q = 1) : d181309 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d129381, d181309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129381, d181309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro40892 (p : Pattern) (ha : d18160 p = 1) (hb : d180908 p = 1) : d181350 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1862 q = 1) : d1862 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1570 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1863 q = 1) (hb : d131097 q = 1) : d19263 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1863, d131097, d19263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1863, d131097, d19263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d18155 q = 1) (hb : d180908 q = 1) : d181345 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18155, d180908, d181345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18155, d180908, d181345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d18156 q = 1) (hb : d180908 q = 1) : d181346 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18156, d181346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18156, d181346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1 q = 1) (hb : d17027 q = 1) : d17027 q = 1 := by
    exact hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d10115 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d17028 q = 1) (hb : d131097 q = 1) : d19266 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d17028, d131097, d19266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d17028, d131097, d19266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d18157 q = 1) (hb : d180908 q = 1) : d181347 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18157, d180908, d181347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d18157, d180908, d181347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h11 (q : Pattern) (ha : d18158 q = 1) (hb : d180908 q = 1) : d181348 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18158, d181348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d18158, d181348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h12 (q : Pattern) (ha : d18159 q = 1) (hb : d180908 q = 1) : d181349 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18159, d181349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d18159, d181349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d1 q = 1) (hb : d15397 q = 1) : d15397 q = 1 := by
    exact hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d10085 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d15398 q = 1) (hb : d131097 q = 1) : d19245 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15398, d131097, d19245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d15398, d131097, d19245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d18139 q = 1) (hb : d180908 q = 1) : d181329 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18139, d180908, d181329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d18139, d180908, d181329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h17 (q : Pattern) (ha : d18140 q = 1) (hb : d180908 q = 1) : d181330 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18140, d181330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d18140, d181330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h18 (q : Pattern) (ha : d18149 q = 1) (hb : d180908 q = 1) : d181339 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18149, d181339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d18149, d181339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h19 (q : Pattern) (ha : d18160 q = 1) (hb : d180908 q = 1) : d181350 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d18160, d181350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d18160, d181350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro40893 (p : Pattern) (ha : d18191 p = 1) (hb : d180908 p = 1) : d181381 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1868 q = 1) : d1868 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1582 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1869 q = 1) (hb : d131097 q = 1) : d19313 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1869, d131097, d19313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1869, d131097, d19313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d18188 q = 1) (hb : d180908 q = 1) : d181378 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18188, d180908, d181378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18188, d180908, d181378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d18189 q = 1) (hb : d180908 q = 1) : d181379 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18189, d181379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18189, d181379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d18190 q = 1) (hb : d180908 q = 1) : d181380 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18190, d181380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d18190, d181380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d1 q = 1) (hb : d15412 q = 1) : d15412 q = 1 := by
    exact hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d10135 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d15413 q = 1) (hb : d131097 q = 1) : d19278 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15413, d131097, d19278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d15413, d131097, d19278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d18167 q = 1) (hb : d180908 q = 1) : d181357 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18167, d180908, d181357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d18167, d180908, d181357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h12 (q : Pattern) (ha : d18168 q = 1) (hb : d180908 q = 1) : d181358 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18168, d181358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d18168, d181358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h13 (q : Pattern) (ha : d18169 q = 1) (hb : d180908 q = 1) : d181359 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18169, d181359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d18169, d181359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h14 (q : Pattern) (ha : d18191 q = 1) (hb : d180908 q = 1) : d181381 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d18191, d181381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d18191, d181381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h14 p ha hb
theorem andIntro40894 (p : Pattern) (ha : d18197 p = 1) (hb : d180908 p = 1) : d181387 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18192 q = 1) (hb : d180908 q = 1) : d181382 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18192, d181382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40892 q ha hb
    | true =>
      simp only [d18192, d181382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40893 q ha hb
  have h2 (q : Pattern) (ha : d18193 q = 1) (hb : d180908 q = 1) : d181383 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18193, d181383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18193, d181383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18194 q = 1) (hb : d180908 q = 1) : d181384 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18194, d181384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18194, d181384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d18195 q = 1) (hb : d180908 q = 1) : d181385 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18195, d181385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18195, d181385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d18196 q = 1) (hb : d180908 q = 1) : d181386 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d18196, d181386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18196, d181386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d18197 q = 1) (hb : d180908 q = 1) : d181387 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d18197, d181387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d18197, d181387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro40895 (p : Pattern) (ha : d18286 p = 1) (hb : d180908 p = 1) : d181419 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18198 q = 1) (hb : d180908 q = 1) : d181388 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18198, d181388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40894 q ha hb
    | true =>
      simp only [d18198, d181388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d18199 q = 1) (hb : d180908 q = 1) : d181389 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18199, d181389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18199, d181389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18283 q = 1) (hb : d180908 q = 1) : d181416 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d18283, d181416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18283, d181416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18284 q = 1) (hb : d180908 q = 1) : d181417 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d18284, d181417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18284, d181417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d18285 q = 1) (hb : d180908 q = 1) : d181418 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d18285, d181418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18285, d181418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d18286 q = 1) (hb : d180908 q = 1) : d181419 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d18286, d181419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d18286, d181419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro40896 (p : Pattern) (ha : d18292 p = 1) (hb : d180908 p = 1) : d181425 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18287 q = 1) (hb : d180908 q = 1) : d181420 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d18287, d181420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40895 q ha hb
    | true =>
      simp only [d18287, d181420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d18288 q = 1) (hb : d180908 q = 1) : d181421 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d18288, d181421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18288, d181421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18289 q = 1) (hb : d180908 q = 1) : d181422 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d18289, d181422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18289, d181422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18290 q = 1) (hb : d180908 q = 1) : d181423 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d18290, d181423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18290, d181423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d18291 q = 1) (hb : d180908 q = 1) : d181424 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d18291, d181424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18291, d181424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d18292 q = 1) (hb : d180908 q = 1) : d181425 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d18292, d181425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18292, d181425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro40897 (p : Pattern) (ha : d18133 p = 1) (hb : d180908 p = 1) : d181323 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1853 q = 1) : d1853 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1665 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1854 q = 1) (hb : d131097 q = 1) : d19223 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1854, d131097, d19223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1854, d131097, d19223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d18123 q = 1) (hb : d180908 q = 1) : d181313 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18123, d180908, d181313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18123, d180908, d181313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d18124 q = 1) (hb : d180908 q = 1) : d181314 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18124, d181314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18124, d181314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1 q = 1) (hb : d17004 q = 1) : d17004 q = 1 := by
    exact hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d10036 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d17005 q = 1) (hb : d131097 q = 1) : d19226 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d17005, d131097, d19226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d17005, d131097, d19226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d18125 q = 1) (hb : d180908 q = 1) : d181315 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18125, d180908, d181315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d18125, d180908, d181315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h11 (q : Pattern) (ha : d18126 q = 1) (hb : d180908 q = 1) : d181316 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18126, d181316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d18126, d181316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h12 (q : Pattern) (ha : d18127 q = 1) (hb : d180908 q = 1) : d181317 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18127, d181317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d18127, d181317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d1 q = 1) (hb : d15380 q = 1) : d15380 q = 1 := by
    exact hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d10046 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d15381 q = 1) (hb : d131097 q = 1) : d19230 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15381, d131097, d19230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d15381, d131097, d19230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d18128 q = 1) (hb : d180908 q = 1) : d181318 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18128, d180908, d181318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d18128, d180908, d181318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h17 (q : Pattern) (ha : d18129 q = 1) (hb : d180908 q = 1) : d181319 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18129, d181319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d18129, d181319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h18 (q : Pattern) (ha : d1 q = 1) (hb : d15387 q = 1) : d15387 q = 1 := by
    exact hb
  have h19 (q : Pattern) (ha : d0 q = 1) (hb : d10063 q = 1) : d0 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d15388 q = 1) (hb : d131097 q = 1) : d19233 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15388, d131097, d19233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
    | true =>
      simp only [d15388, d131097, d19233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
  have h21 (q : Pattern) (ha : d18130 q = 1) (hb : d180908 q = 1) : d181320 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18130, d180908, d181320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d18130, d180908, d181320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h22 (q : Pattern) (ha : d18131 q = 1) (hb : d180908 q = 1) : d181321 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18131, d181321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d18131, d181321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h23 (q : Pattern) (ha : d18132 q = 1) (hb : d180908 q = 1) : d181322 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18132, d181322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d18132, d181322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d18133 q = 1) (hb : d180908 q = 1) : d181323 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d18133, d181323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d18133, d181323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  exact h24 p ha hb
theorem andIntro40898 (p : Pattern) (ha : d18142 p = 1) (hb : d180908 p = 1) : d181332 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1857 q = 1) : d1857 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1555 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1858 q = 1) (hb : d131097 q = 1) : d19238 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1858, d131097, d19238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1858, d131097, d19238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d18134 q = 1) (hb : d180908 q = 1) : d181324 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18134, d180908, d181324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18134, d180908, d181324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d18135 q = 1) (hb : d180908 q = 1) : d181325 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18135, d181325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18135, d181325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1 q = 1) (hb : d17011 q = 1) : d17011 q = 1 := by
    exact hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d10074 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d17012 q = 1) (hb : d131097 q = 1) : d19241 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d17012, d131097, d19241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d17012, d131097, d19241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d18136 q = 1) (hb : d180908 q = 1) : d181326 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18136, d180908, d181326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d18136, d180908, d181326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h11 (q : Pattern) (ha : d18137 q = 1) (hb : d180908 q = 1) : d181327 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18137, d181327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d18137, d181327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h12 (q : Pattern) (ha : d18138 q = 1) (hb : d180908 q = 1) : d181328 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18138, d181328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d18138, d181328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d1 q = 1) (hb : d15387 q = 1) : d15387 q = 1 := by
    exact hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d10063 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d15388 q = 1) (hb : d131097 q = 1) : d19233 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15388, d131097, d19233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d15388, d131097, d19233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d18130 q = 1) (hb : d180908 q = 1) : d181320 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18130, d180908, d181320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d18130, d180908, d181320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h17 (q : Pattern) (ha : d18131 q = 1) (hb : d180908 q = 1) : d181321 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18131, d181321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d18131, d181321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h18 (q : Pattern) (ha : d1 q = 1) (hb : d15397 q = 1) : d15397 q = 1 := by
    exact hb
  have h19 (q : Pattern) (ha : d0 q = 1) (hb : d10085 q = 1) : d0 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d15398 q = 1) (hb : d131097 q = 1) : d19245 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15398, d131097, d19245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
    | true =>
      simp only [d15398, d131097, d19245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
  have h21 (q : Pattern) (ha : d18139 q = 1) (hb : d180908 q = 1) : d181329 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18139, d180908, d181329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d18139, d180908, d181329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h22 (q : Pattern) (ha : d18140 q = 1) (hb : d180908 q = 1) : d181330 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18140, d181330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d18140, d181330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h23 (q : Pattern) (ha : d18141 q = 1) (hb : d180908 q = 1) : d181331 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18141, d181331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d18141, d181331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d18142 q = 1) (hb : d180908 q = 1) : d181332 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d18142, d181332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d18142, d181332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  exact h24 p ha hb
theorem andIntro40899 (p : Pattern) (ha : d18150 p = 1) (hb : d180908 p = 1) : d181340 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d13486 q = 1) : d13486 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d10099 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d13487 q = 1) (hb : d131097 q = 1) : d19253 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13487, d131097, d19253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d13487, d131097, d19253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d18146 q = 1) (hb : d180908 q = 1) : d181336 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18146, d180908, d181336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18146, d180908, d181336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d18147 q = 1) (hb : d180908 q = 1) : d181337 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18147, d181337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18147, d181337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1 q = 1) (hb : d15397 q = 1) : d15397 q = 1 := by
    exact hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d10085 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d15398 q = 1) (hb : d131097 q = 1) : d19245 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15398, d131097, d19245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d15398, d131097, d19245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d18139 q = 1) (hb : d180908 q = 1) : d181329 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18139, d180908, d181329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d18139, d180908, d181329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h11 (q : Pattern) (ha : d18140 q = 1) (hb : d180908 q = 1) : d181330 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18140, d181330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d18140, d181330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h12 (q : Pattern) (ha : d18148 q = 1) (hb : d180908 q = 1) : d181338 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18148, d181338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d18148, d181338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d18149 q = 1) (hb : d180908 q = 1) : d181339 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18149, d181339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d18149, d181339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h14 (q : Pattern) (ha : d18150 q = 1) (hb : d180908 q = 1) : d181340 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d18150, d181340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d18150, d181340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h14 p ha hb
theorem andIntro40900 (p : Pattern) (ha : d18170 p = 1) (hb : d180908 p = 1) : d181360 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d6496 q = 1) : d6496 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d5134 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d6497 q = 1) (hb : d131097 q = 1) : d19274 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d6497, d131097, d19274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d6497, d131097, d19274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d18164 q = 1) (hb : d180908 q = 1) : d181354 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18164, d180908, d181354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18164, d180908, d181354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d18165 q = 1) (hb : d180908 q = 1) : d181355 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18165, d181355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18165, d181355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d18166 q = 1) (hb : d180908 q = 1) : d181356 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18166, d181356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d18166, d181356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d1 q = 1) (hb : d15412 q = 1) : d15412 q = 1 := by
    exact hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d10135 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d15413 q = 1) (hb : d131097 q = 1) : d19278 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15413, d131097, d19278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d15413, d131097, d19278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d18167 q = 1) (hb : d180908 q = 1) : d181357 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18167, d180908, d181357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d18167, d180908, d181357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h12 (q : Pattern) (ha : d18168 q = 1) (hb : d180908 q = 1) : d181358 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18168, d181358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d18168, d181358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h13 (q : Pattern) (ha : d18169 q = 1) (hb : d180908 q = 1) : d181359 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18169, d181359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d18169, d181359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h14 (q : Pattern) (ha : d18170 q = 1) (hb : d180908 q = 1) : d181360 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d18170, d181360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d18170, d181360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h14 p ha hb
theorem andIntro40901 (p : Pattern) (ha : d18176 p = 1) (hb : d180908 p = 1) : d181366 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18143 q = 1) (hb : d180908 q = 1) : d181333 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18143, d181333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40897 q ha hb
    | true =>
      simp only [d18143, d181333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40898 q ha hb
  have h2 (q : Pattern) (ha : d18144 q = 1) (hb : d180908 q = 1) : d181334 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18144, d181334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18144, d181334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18145 q = 1) (hb : d180908 q = 1) : d181335 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18145, d181335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18145, d181335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d18151 q = 1) (hb : d180908 q = 1) : d181341 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18151, d181341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40898 q ha hb
    | true =>
      simp only [d18151, d181341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40899 q ha hb
  have h5 (q : Pattern) (ha : d18152 q = 1) (hb : d180908 q = 1) : d181342 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18152, d181342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18152, d181342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d18153 q = 1) (hb : d180908 q = 1) : d181343 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18153, d181343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18153, d181343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d18154 q = 1) (hb : d180908 q = 1) : d181344 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18154, d181344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18154, d181344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d18161 q = 1) (hb : d180908 q = 1) : d181351 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18161, d181351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40898 q ha hb
    | true =>
      simp only [d18161, d181351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40892 q ha hb
  have h9 (q : Pattern) (ha : d18162 q = 1) (hb : d180908 q = 1) : d181352 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18162, d181352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18162, d181352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d18163 q = 1) (hb : d180908 q = 1) : d181353 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18163, d181353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18163, d181353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d18171 q = 1) (hb : d180908 q = 1) : d181361 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18171, d181361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40892 q ha hb
    | true =>
      simp only [d18171, d181361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40900 q ha hb
  have h12 (q : Pattern) (ha : d18172 q = 1) (hb : d180908 q = 1) : d181362 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18172, d181362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18172, d181362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d18173 q = 1) (hb : d180908 q = 1) : d181363 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18173, d181363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18173, d181363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d18174 q = 1) (hb : d180908 q = 1) : d181364 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18174, d181364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d18174, d181364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d18175 q = 1) (hb : d180908 q = 1) : d181365 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d18175, d181365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d18175, d181365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d18176 q = 1) (hb : d180908 q = 1) : d181366 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d18176, d181366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d18176, d181366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro40902 (p : Pattern) (ha : d18181 p = 1) (hb : d180908 p = 1) : d181371 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18161 q = 1) (hb : d180908 q = 1) : d181351 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18161, d181351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40898 q ha hb
    | true =>
      simp only [d18161, d181351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40892 q ha hb
  have h2 (q : Pattern) (ha : d18162 q = 1) (hb : d180908 q = 1) : d181352 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18162, d181352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18162, d181352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18163 q = 1) (hb : d180908 q = 1) : d181353 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18163, d181353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18163, d181353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d18171 q = 1) (hb : d180908 q = 1) : d181361 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18171, d181361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40892 q ha hb
    | true =>
      simp only [d18171, d181361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40900 q ha hb
  have h5 (q : Pattern) (ha : d18172 q = 1) (hb : d180908 q = 1) : d181362 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18172, d181362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18172, d181362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d18173 q = 1) (hb : d180908 q = 1) : d181363 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18173, d181363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18173, d181363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d18174 q = 1) (hb : d180908 q = 1) : d181364 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18174, d181364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18174, d181364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d18179 q = 1) (hb : d180908 q = 1) : d181369 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18179, d181369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d18179, d181369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d18180 q = 1) (hb : d180908 q = 1) : d181370 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d18180, d181370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d18180, d181370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d18181 q = 1) (hb : d180908 q = 1) : d181371 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d18181, d181371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d18181, d181371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro40903 (p : Pattern) (ha : d18187 p = 1) (hb : d180908 p = 1) : d181377 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18177 q = 1) (hb : d180908 q = 1) : d181367 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18177, d181367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40901 q ha hb
    | true =>
      simp only [d18177, d181367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d18178 q = 1) (hb : d180908 q = 1) : d181368 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18178, d181368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18178, d181368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18182 q = 1) (hb : d180908 q = 1) : d181372 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18182, d181372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40902 q ha hb
    | true =>
      simp only [d18182, d181372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18183 q = 1) (hb : d180908 q = 1) : d181373 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18183, d181373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18183, d181373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d18184 q = 1) (hb : d180908 q = 1) : d181374 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d18184, d181374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18184, d181374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d18185 q = 1) (hb : d180908 q = 1) : d181375 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d18185, d181375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d18185, d181375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d18186 q = 1) (hb : d180908 q = 1) : d181376 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d18186, d181376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d18186, d181376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d18187 q = 1) (hb : d180908 q = 1) : d181377 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d18187, d181377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d18187, d181377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro40904 (p : Pattern) (ha : d18203 p = 1) (hb : d180908 p = 1) : d181393 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18182 q = 1) (hb : d180908 q = 1) : d181372 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18182, d181372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40902 q ha hb
    | true =>
      simp only [d18182, d181372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d18183 q = 1) (hb : d180908 q = 1) : d181373 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18183, d181373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18183, d181373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18198 q = 1) (hb : d180908 q = 1) : d181388 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18198, d181388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40894 q ha hb
    | true =>
      simp only [d18198, d181388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18199 q = 1) (hb : d180908 q = 1) : d181389 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18199, d181389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18199, d181389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d18200 q = 1) (hb : d180908 q = 1) : d181390 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d18200, d181390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18200, d181390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d18201 q = 1) (hb : d180908 q = 1) : d181391 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d18201, d181391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d18201, d181391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d18202 q = 1) (hb : d180908 q = 1) : d181392 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d18202, d181392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d18202, d181392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d18203 q = 1) (hb : d180908 q = 1) : d181393 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d18203, d181393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d18203, d181393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro40905 (p : Pattern) (ha : d18263 p = 1) (hb : d180908 p = 1) : d181396 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1868 q = 1) : d1868 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1582 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1869 q = 1) (hb : d131097 q = 1) : d19313 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1869, d131097, d19313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1869, d131097, d19313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d18188 q = 1) (hb : d180908 q = 1) : d181378 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18188, d180908, d181378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18188, d180908, d181378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d18189 q = 1) (hb : d180908 q = 1) : d181379 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18189, d181379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18189, d181379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d18190 q = 1) (hb : d180908 q = 1) : d181380 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18190, d181380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d18190, d181380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d18263 q = 1) (hb : d180908 q = 1) : d181396 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d18263, d181396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d18263, d181396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro40906 (p : Pattern) (ha : d18269 p = 1) (hb : d180908 p = 1) : d181402 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18161 q = 1) (hb : d180908 q = 1) : d181351 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18161, d181351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40898 q ha hb
    | true =>
      simp only [d18161, d181351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40892 q ha hb
  have h2 (q : Pattern) (ha : d18162 q = 1) (hb : d180908 q = 1) : d181352 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18162, d181352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18162, d181352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18163 q = 1) (hb : d180908 q = 1) : d181353 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18163, d181353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18163, d181353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d18171 q = 1) (hb : d180908 q = 1) : d181361 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18171, d181361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40892 q ha hb
    | true =>
      simp only [d18171, d181361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40900 q ha hb
  have h5 (q : Pattern) (ha : d18172 q = 1) (hb : d180908 q = 1) : d181362 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18172, d181362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18172, d181362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d18173 q = 1) (hb : d180908 q = 1) : d181363 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18173, d181363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18173, d181363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d18174 q = 1) (hb : d180908 q = 1) : d181364 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18174, d181364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18174, d181364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d18264 q = 1) (hb : d180908 q = 1) : d181397 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18264, d181397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40892 q ha hb
    | true =>
      simp only [d18264, d181397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40905 q ha hb
  have h9 (q : Pattern) (ha : d18265 q = 1) (hb : d180908 q = 1) : d181398 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18265, d181398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18265, d181398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d18266 q = 1) (hb : d180908 q = 1) : d181399 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18266, d181399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18266, d181399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d18267 q = 1) (hb : d180908 q = 1) : d181400 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18267, d181400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d18267, d181400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d18268 q = 1) (hb : d180908 q = 1) : d181401 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d18268, d181401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d18268, d181401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d18269 q = 1) (hb : d180908 q = 1) : d181402 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d18269, d181402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d18269, d181402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro40907 (p : Pattern) (ha : d18275 p = 1) (hb : d180908 p = 1) : d181408 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18270 q = 1) (hb : d180908 q = 1) : d181403 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18270, d181403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40906 q ha hb
    | true =>
      simp only [d18270, d181403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d18271 q = 1) (hb : d180908 q = 1) : d181404 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18271, d181404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18271, d181404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18272 q = 1) (hb : d180908 q = 1) : d181405 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d18272, d181405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18272, d181405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18273 q = 1) (hb : d180908 q = 1) : d181406 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d18273, d181406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18273, d181406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d18274 q = 1) (hb : d180908 q = 1) : d181407 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d18274, d181407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18274, d181407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d18275 q = 1) (hb : d180908 q = 1) : d181408 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d18275, d181408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d18275, d181408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro40908 (p : Pattern) (ha : d129389 p = 1) (hb : d180908 p = 1) : d181414 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18204 q = 1) (hb : d180908 q = 1) : d181394 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d18204, d181394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40903 q ha hb
    | true =>
      simp only [d18204, d181394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40904 q ha hb
  have h2 (q : Pattern) (ha : d129385 q = 1) (hb : d180908 q = 1) : d181395 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d129385, d181395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129385, d181395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d18276 q = 1) (hb : d180908 q = 1) : d181409 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d18276, d181409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40907 q ha hb
    | true =>
      simp only [d18276, d181409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18277 q = 1) (hb : d180908 q = 1) : d181410 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d18277, d181410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18277, d181410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d129386 q = 1) (hb : d180908 q = 1) : d181411 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d129386, d181411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129386, d181411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129387 q = 1) (hb : d180908 q = 1) : d181412 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d129387, d181412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129387, d181412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d129388 q = 1) (hb : d180908 q = 1) : d181413 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d129388, d181413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129388, d181413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d129389 q = 1) (hb : d180908 q = 1) : d181414 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d129389, d181414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129389, d181414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro40909 (p : Pattern) (ha : d129395 p = 1) (hb : d180908 p = 1) : d181431 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129390 q = 1) (hb : d180908 q = 1) : d181415 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d129390, d181415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129390, d181415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40908 q ha hb
  have h2 (q : Pattern) (ha : d18293 q = 1) (hb : d180908 q = 1) : d181426 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d18293, d181426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18293, d181426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40896 q ha hb
  have h3 (q : Pattern) (ha : d129391 q = 1) (hb : d180908 q = 1) : d181427 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d129391, d181427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129391, d181427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d129392 q = 1) (hb : d180908 q = 1) : d181428 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d129392, d181428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129392, d181428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d129393 q = 1) (hb : d180908 q = 1) : d181429 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d129393, d181429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129393, d181429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d129394 q = 1) (hb : d180908 q = 1) : d181430 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d129394, d181430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129394, d181430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d129395 q = 1) (hb : d180908 q = 1) : d181431 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d129395, d181431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129395, d181431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro40910 (p : Pattern) (ha : d129401 p = 1) (hb : d180908 p = 1) : d181437 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129396 q = 1) (hb : d180908 q = 1) : d181432 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d129396, d181432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129396, d181432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40909 q ha hb
  have h2 (q : Pattern) (ha : d129397 q = 1) (hb : d180908 q = 1) : d181433 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d129397, d181433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129397, d181433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d129398 q = 1) (hb : d180908 q = 1) : d181434 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d129398, d181434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129398, d181434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d129399 q = 1) (hb : d180908 q = 1) : d181435 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d129399, d181435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129399, d181435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129400 q = 1) (hb : d180908 q = 1) : d181436 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d129400, d181436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129400, d181436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129401 q = 1) (hb : d180908 q = 1) : d181437 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d129401, d181437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129401, d181437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro40911 (p : Pattern) (ha : d18341 p = 1) (hb : d180908 p = 1) : d181474 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d2340 q = 1) : d2340 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2053 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2341 q = 1) (hb : d131097 q = 1) : d19495 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2341, d131097, d19495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d2341, d131097, d19495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d18336 q = 1) (hb : d180908 q = 1) : d181469 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18336, d180908, d181469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18336, d180908, d181469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d18337 q = 1) (hb : d180908 q = 1) : d181470 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18337, d181470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18337, d181470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1 q = 1) (hb : d17391 q = 1) : d17391 q = 1 := by
    exact hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d10391 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d17392 q = 1) (hb : d131097 q = 1) : d19498 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d17392, d131097, d19498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d17392, d131097, d19498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d18338 q = 1) (hb : d180908 q = 1) : d181471 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18338, d180908, d181471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d18338, d180908, d181471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h11 (q : Pattern) (ha : d18339 q = 1) (hb : d180908 q = 1) : d181472 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18339, d181472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d18339, d181472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h12 (q : Pattern) (ha : d18340 q = 1) (hb : d180908 q = 1) : d181473 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18340, d181473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d18340, d181473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d1 q = 1) (hb : d15775 q = 1) : d15775 q = 1 := by
    exact hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d10371 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d15776 q = 1) (hb : d131097 q = 1) : d19481 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15776, d131097, d19481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d15776, d131097, d19481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d18323 q = 1) (hb : d180908 q = 1) : d181456 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18323, d180908, d181456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d18323, d180908, d181456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h17 (q : Pattern) (ha : d18324 q = 1) (hb : d180908 q = 1) : d181457 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18324, d181457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d18324, d181457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h18 (q : Pattern) (ha : d18330 q = 1) (hb : d180908 q = 1) : d181463 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18330, d181463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d18330, d181463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h19 (q : Pattern) (ha : d18341 q = 1) (hb : d180908 q = 1) : d181474 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d18341, d181474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d18341, d181474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro40912 (p : Pattern) (ha : d18372 p = 1) (hb : d180908 p = 1) : d181505 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d2346 q = 1) : d2346 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2065 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2347 q = 1) (hb : d131097 q = 1) : d19545 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2347, d131097, d19545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d2347, d131097, d19545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d18369 q = 1) (hb : d180908 q = 1) : d181502 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18369, d180908, d181502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18369, d180908, d181502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d18370 q = 1) (hb : d180908 q = 1) : d181503 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18370, d181503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18370, d181503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d18371 q = 1) (hb : d180908 q = 1) : d181504 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18371, d181504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d18371, d181504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d1 q = 1) (hb : d15790 q = 1) : d15790 q = 1 := by
    exact hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d10412 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d15791 q = 1) (hb : d131097 q = 1) : d19510 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15791, d131097, d19510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d15791, d131097, d19510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d18348 q = 1) (hb : d180908 q = 1) : d181481 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18348, d180908, d181481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d18348, d180908, d181481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h12 (q : Pattern) (ha : d18349 q = 1) (hb : d180908 q = 1) : d181482 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18349, d181482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d18349, d181482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h13 (q : Pattern) (ha : d18350 q = 1) (hb : d180908 q = 1) : d181483 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18350, d181483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d18350, d181483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h14 (q : Pattern) (ha : d18372 q = 1) (hb : d180908 q = 1) : d181505 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d18372, d181505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d18372, d181505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h14 p ha hb
theorem andIntro40913 (p : Pattern) (ha : d18378 p = 1) (hb : d180908 p = 1) : d181511 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18373 q = 1) (hb : d180908 q = 1) : d181506 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18373, d181506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40911 q ha hb
    | true =>
      simp only [d18373, d181506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40912 q ha hb
  have h2 (q : Pattern) (ha : d18374 q = 1) (hb : d180908 q = 1) : d181507 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18374, d181507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18374, d181507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18375 q = 1) (hb : d180908 q = 1) : d181508 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18375, d181508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18375, d181508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d18376 q = 1) (hb : d180908 q = 1) : d181509 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18376, d181509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18376, d181509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d18377 q = 1) (hb : d180908 q = 1) : d181510 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d18377, d181510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18377, d181510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d18378 q = 1) (hb : d180908 q = 1) : d181511 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d18378, d181511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d18378, d181511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro40914 (p : Pattern) (ha : d18467 p = 1) (hb : d180908 p = 1) : d181543 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18379 q = 1) (hb : d180908 q = 1) : d181512 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18379, d181512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40913 q ha hb
    | true =>
      simp only [d18379, d181512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d18380 q = 1) (hb : d180908 q = 1) : d181513 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18380, d181513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18380, d181513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18464 q = 1) (hb : d180908 q = 1) : d181540 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d18464, d181540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18464, d181540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18465 q = 1) (hb : d180908 q = 1) : d181541 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d18465, d181541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18465, d181541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d18466 q = 1) (hb : d180908 q = 1) : d181542 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d18466, d181542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18466, d181542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d18467 q = 1) (hb : d180908 q = 1) : d181543 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d18467, d181543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d18467, d181543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro40915 (p : Pattern) (ha : d18473 p = 1) (hb : d180908 p = 1) : d181549 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18468 q = 1) (hb : d180908 q = 1) : d181544 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d18468, d181544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40914 q ha hb
    | true =>
      simp only [d18468, d181544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d18469 q = 1) (hb : d180908 q = 1) : d181545 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d18469, d181545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18469, d181545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18470 q = 1) (hb : d180908 q = 1) : d181546 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d18470, d181546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18470, d181546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18471 q = 1) (hb : d180908 q = 1) : d181547 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d18471, d181547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18471, d181547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d18472 q = 1) (hb : d180908 q = 1) : d181548 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d18472, d181548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18472, d181548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d18473 q = 1) (hb : d180908 q = 1) : d181549 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d18473, d181549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18473, d181549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro40916 (p : Pattern) (ha : d18317 p = 1) (hb : d180908 p = 1) : d181450 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d2331 q = 1) : d2331 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2144 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2332 q = 1) (hb : d131097 q = 1) : d19462 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2332, d131097, d19462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d2332, d131097, d19462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d18309 q = 1) (hb : d180908 q = 1) : d181442 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18309, d180908, d181442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18309, d180908, d181442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d18310 q = 1) (hb : d180908 q = 1) : d181443 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18310, d181443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18310, d181443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1 q = 1) (hb : d17369 q = 1) : d17369 q = 1 := by
    exact hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d10343 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d17370 q = 1) (hb : d131097 q = 1) : d19465 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d17370, d131097, d19465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d17370, d131097, d19465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d18311 q = 1) (hb : d180908 q = 1) : d181444 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18311, d180908, d181444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d18311, d180908, d181444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h11 (q : Pattern) (ha : d18312 q = 1) (hb : d180908 q = 1) : d181445 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18312, d181445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d18312, d181445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h12 (q : Pattern) (ha : d18313 q = 1) (hb : d180908 q = 1) : d181446 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18313, d181446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d18313, d181446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d1 q = 1) (hb : d13813 q = 1) : d13813 q = 1 := by
    exact hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d10353 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d13814 q = 1) (hb : d131097 q = 1) : d19469 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13814, d131097, d19469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d13814, d131097, d19469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d18314 q = 1) (hb : d180908 q = 1) : d181447 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18314, d180908, d181447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d18314, d180908, d181447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h17 (q : Pattern) (ha : d18315 q = 1) (hb : d180908 q = 1) : d181448 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18315, d181448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d18315, d181448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h18 (q : Pattern) (ha : d18316 q = 1) (hb : d180908 q = 1) : d181449 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18316, d181449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d18316, d181449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d18317 q = 1) (hb : d180908 q = 1) : d181450 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d18317, d181450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d18317, d181450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro40917 (p : Pattern) (ha : d18326 p = 1) (hb : d180908 p = 1) : d181459 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d2335 q = 1) : d2335 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2035 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2336 q = 1) (hb : d131097 q = 1) : d19474 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2336, d131097, d19474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d2336, d131097, d19474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d18318 q = 1) (hb : d180908 q = 1) : d181451 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18318, d180908, d181451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18318, d180908, d181451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d18319 q = 1) (hb : d180908 q = 1) : d181452 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18319, d181452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18319, d181452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1 q = 1) (hb : d17376 q = 1) : d17376 q = 1 := by
    exact hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d10364 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d17377 q = 1) (hb : d131097 q = 1) : d19477 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d17377, d131097, d19477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d17377, d131097, d19477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d18320 q = 1) (hb : d180908 q = 1) : d181453 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18320, d180908, d181453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d18320, d180908, d181453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h11 (q : Pattern) (ha : d18321 q = 1) (hb : d180908 q = 1) : d181454 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18321, d181454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d18321, d181454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h12 (q : Pattern) (ha : d18322 q = 1) (hb : d180908 q = 1) : d181455 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18322, d181455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d18322, d181455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d1 q = 1) (hb : d13813 q = 1) : d13813 q = 1 := by
    exact hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d10353 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d13814 q = 1) (hb : d131097 q = 1) : d19469 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13814, d131097, d19469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d13814, d131097, d19469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d18314 q = 1) (hb : d180908 q = 1) : d181447 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18314, d180908, d181447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d18314, d180908, d181447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h17 (q : Pattern) (ha : d18315 q = 1) (hb : d180908 q = 1) : d181448 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18315, d181448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d18315, d181448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h18 (q : Pattern) (ha : d1 q = 1) (hb : d15775 q = 1) : d15775 q = 1 := by
    exact hb
  have h19 (q : Pattern) (ha : d0 q = 1) (hb : d10371 q = 1) : d0 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d15776 q = 1) (hb : d131097 q = 1) : d19481 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15776, d131097, d19481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
    | true =>
      simp only [d15776, d131097, d19481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
  have h21 (q : Pattern) (ha : d18323 q = 1) (hb : d180908 q = 1) : d181456 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18323, d180908, d181456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d18323, d180908, d181456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h22 (q : Pattern) (ha : d18324 q = 1) (hb : d180908 q = 1) : d181457 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18324, d181457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d18324, d181457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h23 (q : Pattern) (ha : d18325 q = 1) (hb : d180908 q = 1) : d181458 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18325, d181458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d18325, d181458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d18326 q = 1) (hb : d180908 q = 1) : d181459 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d18326, d181459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d18326, d181459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  exact h24 p ha hb
theorem andIntro40918 (p : Pattern) (ha : d18331 p = 1) (hb : d180908 p = 1) : d181464 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d13813 q = 1) : d13813 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d10353 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d13814 q = 1) (hb : d131097 q = 1) : d19469 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13814, d131097, d19469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d13814, d131097, d19469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d18314 q = 1) (hb : d180908 q = 1) : d181447 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18314, d180908, d181447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18314, d180908, d181447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d18315 q = 1) (hb : d180908 q = 1) : d181448 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18315, d181448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18315, d181448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1 q = 1) (hb : d15775 q = 1) : d15775 q = 1 := by
    exact hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d10371 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d15776 q = 1) (hb : d131097 q = 1) : d19481 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15776, d131097, d19481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d15776, d131097, d19481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d18323 q = 1) (hb : d180908 q = 1) : d181456 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18323, d180908, d181456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d18323, d180908, d181456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h11 (q : Pattern) (ha : d18324 q = 1) (hb : d180908 q = 1) : d181457 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18324, d181457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d18324, d181457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h12 (q : Pattern) (ha : d18325 q = 1) (hb : d180908 q = 1) : d181458 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18325, d181458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d18325, d181458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d18330 q = 1) (hb : d180908 q = 1) : d181463 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18330, d181463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d18330, d181463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h14 (q : Pattern) (ha : d18331 q = 1) (hb : d180908 q = 1) : d181464 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d18331, d181464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d18331, d181464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h14 p ha hb
theorem andIntro40919 (p : Pattern) (ha : d18351 p = 1) (hb : d180908 p = 1) : d181484 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d6643 q = 1) : d6643 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d5247 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d6644 q = 1) (hb : d131097 q = 1) : d19506 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d6644, d131097, d19506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d6644, d131097, d19506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d18345 q = 1) (hb : d180908 q = 1) : d181478 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18345, d180908, d181478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18345, d180908, d181478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d18346 q = 1) (hb : d180908 q = 1) : d181479 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18346, d181479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18346, d181479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d18347 q = 1) (hb : d180908 q = 1) : d181480 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18347, d181480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d18347, d181480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d1 q = 1) (hb : d15790 q = 1) : d15790 q = 1 := by
    exact hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d10412 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d15791 q = 1) (hb : d131097 q = 1) : d19510 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15791, d131097, d19510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d15791, d131097, d19510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d18348 q = 1) (hb : d180908 q = 1) : d181481 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18348, d180908, d181481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d18348, d180908, d181481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h12 (q : Pattern) (ha : d18349 q = 1) (hb : d180908 q = 1) : d181482 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18349, d181482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d18349, d181482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h13 (q : Pattern) (ha : d18350 q = 1) (hb : d180908 q = 1) : d181483 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18350, d181483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d18350, d181483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h14 (q : Pattern) (ha : d18351 q = 1) (hb : d180908 q = 1) : d181484 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d18351, d181484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d18351, d181484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h14 p ha hb
theorem andIntro40920 (p : Pattern) (ha : d18357 p = 1) (hb : d180908 p = 1) : d181490 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18327 q = 1) (hb : d180908 q = 1) : d181460 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18327, d181460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40916 q ha hb
    | true =>
      simp only [d18327, d181460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40917 q ha hb
  have h2 (q : Pattern) (ha : d18328 q = 1) (hb : d180908 q = 1) : d181461 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18328, d181461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18328, d181461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18329 q = 1) (hb : d180908 q = 1) : d181462 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18329, d181462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18329, d181462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d18332 q = 1) (hb : d180908 q = 1) : d181465 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18332, d181465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40917 q ha hb
    | true =>
      simp only [d18332, d181465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40918 q ha hb
  have h5 (q : Pattern) (ha : d18333 q = 1) (hb : d180908 q = 1) : d181466 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18333, d181466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18333, d181466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d18334 q = 1) (hb : d180908 q = 1) : d181467 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18334, d181467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18334, d181467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d18335 q = 1) (hb : d180908 q = 1) : d181468 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18335, d181468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18335, d181468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d18342 q = 1) (hb : d180908 q = 1) : d181475 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18342, d181475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40917 q ha hb
    | true =>
      simp only [d18342, d181475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40911 q ha hb
  have h9 (q : Pattern) (ha : d18343 q = 1) (hb : d180908 q = 1) : d181476 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18343, d181476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18343, d181476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d18344 q = 1) (hb : d180908 q = 1) : d181477 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18344, d181477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18344, d181477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d18352 q = 1) (hb : d180908 q = 1) : d181485 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18352, d181485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40911 q ha hb
    | true =>
      simp only [d18352, d181485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40919 q ha hb
  have h12 (q : Pattern) (ha : d18353 q = 1) (hb : d180908 q = 1) : d181486 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18353, d181486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18353, d181486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d18354 q = 1) (hb : d180908 q = 1) : d181487 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18354, d181487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18354, d181487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d18355 q = 1) (hb : d180908 q = 1) : d181488 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18355, d181488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d18355, d181488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d18356 q = 1) (hb : d180908 q = 1) : d181489 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d18356, d181489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d18356, d181489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d18357 q = 1) (hb : d180908 q = 1) : d181490 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d18357, d181490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d18357, d181490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro40921 (p : Pattern) (ha : d18362 p = 1) (hb : d180908 p = 1) : d181495 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18342 q = 1) (hb : d180908 q = 1) : d181475 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18342, d181475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40917 q ha hb
    | true =>
      simp only [d18342, d181475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40911 q ha hb
  have h2 (q : Pattern) (ha : d18343 q = 1) (hb : d180908 q = 1) : d181476 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18343, d181476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18343, d181476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18344 q = 1) (hb : d180908 q = 1) : d181477 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18344, d181477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18344, d181477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d18352 q = 1) (hb : d180908 q = 1) : d181485 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18352, d181485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40911 q ha hb
    | true =>
      simp only [d18352, d181485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40919 q ha hb
  have h5 (q : Pattern) (ha : d18353 q = 1) (hb : d180908 q = 1) : d181486 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18353, d181486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18353, d181486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d18354 q = 1) (hb : d180908 q = 1) : d181487 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18354, d181487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18354, d181487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d18355 q = 1) (hb : d180908 q = 1) : d181488 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18355, d181488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18355, d181488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d18360 q = 1) (hb : d180908 q = 1) : d181493 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18360, d181493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d18360, d181493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d18361 q = 1) (hb : d180908 q = 1) : d181494 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d18361, d181494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d18361, d181494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d18362 q = 1) (hb : d180908 q = 1) : d181495 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d18362, d181495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d18362, d181495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro40922 (p : Pattern) (ha : d18368 p = 1) (hb : d180908 p = 1) : d181501 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18358 q = 1) (hb : d180908 q = 1) : d181491 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18358, d181491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40920 q ha hb
    | true =>
      simp only [d18358, d181491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d18359 q = 1) (hb : d180908 q = 1) : d181492 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18359, d181492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18359, d181492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18363 q = 1) (hb : d180908 q = 1) : d181496 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18363, d181496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40921 q ha hb
    | true =>
      simp only [d18363, d181496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18364 q = 1) (hb : d180908 q = 1) : d181497 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18364, d181497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18364, d181497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d18365 q = 1) (hb : d180908 q = 1) : d181498 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d18365, d181498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18365, d181498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d18366 q = 1) (hb : d180908 q = 1) : d181499 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d18366, d181499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d18366, d181499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d18367 q = 1) (hb : d180908 q = 1) : d181500 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d18367, d181500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d18367, d181500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d18368 q = 1) (hb : d180908 q = 1) : d181501 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d18368, d181501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d18368, d181501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro40923 (p : Pattern) (ha : d18384 p = 1) (hb : d180908 p = 1) : d181517 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18363 q = 1) (hb : d180908 q = 1) : d181496 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18363, d181496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40921 q ha hb
    | true =>
      simp only [d18363, d181496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d18364 q = 1) (hb : d180908 q = 1) : d181497 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18364, d181497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18364, d181497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18379 q = 1) (hb : d180908 q = 1) : d181512 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18379, d181512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40913 q ha hb
    | true =>
      simp only [d18379, d181512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18380 q = 1) (hb : d180908 q = 1) : d181513 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18380, d181513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18380, d181513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d18381 q = 1) (hb : d180908 q = 1) : d181514 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d18381, d181514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18381, d181514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d18382 q = 1) (hb : d180908 q = 1) : d181515 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d18382, d181515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d18382, d181515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d18383 q = 1) (hb : d180908 q = 1) : d181516 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d18383, d181516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d18383, d181516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d18384 q = 1) (hb : d180908 q = 1) : d181517 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d18384, d181517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d18384, d181517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro40924 (p : Pattern) (ha : d18444 p = 1) (hb : d180908 p = 1) : d181520 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d2346 q = 1) : d2346 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2065 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2347 q = 1) (hb : d131097 q = 1) : d19545 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2347, d131097, d19545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d2347, d131097, d19545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d18369 q = 1) (hb : d180908 q = 1) : d181502 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18369, d180908, d181502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18369, d180908, d181502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d18370 q = 1) (hb : d180908 q = 1) : d181503 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18370, d181503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18370, d181503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d18371 q = 1) (hb : d180908 q = 1) : d181504 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18371, d181504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d18371, d181504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d18444 q = 1) (hb : d180908 q = 1) : d181520 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d18444, d181520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d18444, d181520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro40925 (p : Pattern) (ha : d18450 p = 1) (hb : d180908 p = 1) : d181526 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18342 q = 1) (hb : d180908 q = 1) : d181475 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18342, d181475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40917 q ha hb
    | true =>
      simp only [d18342, d181475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40911 q ha hb
  have h2 (q : Pattern) (ha : d18343 q = 1) (hb : d180908 q = 1) : d181476 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18343, d181476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18343, d181476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18344 q = 1) (hb : d180908 q = 1) : d181477 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18344, d181477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18344, d181477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d18352 q = 1) (hb : d180908 q = 1) : d181485 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18352, d181485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40911 q ha hb
    | true =>
      simp only [d18352, d181485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40919 q ha hb
  have h5 (q : Pattern) (ha : d18353 q = 1) (hb : d180908 q = 1) : d181486 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18353, d181486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18353, d181486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d18354 q = 1) (hb : d180908 q = 1) : d181487 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18354, d181487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18354, d181487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d18355 q = 1) (hb : d180908 q = 1) : d181488 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18355, d181488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18355, d181488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d18445 q = 1) (hb : d180908 q = 1) : d181521 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18445, d181521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40911 q ha hb
    | true =>
      simp only [d18445, d181521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40924 q ha hb
  have h9 (q : Pattern) (ha : d18446 q = 1) (hb : d180908 q = 1) : d181522 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18446, d181522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18446, d181522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d18447 q = 1) (hb : d180908 q = 1) : d181523 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18447, d181523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18447, d181523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d18448 q = 1) (hb : d180908 q = 1) : d181524 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18448, d181524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d18448, d181524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d18449 q = 1) (hb : d180908 q = 1) : d181525 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d18449, d181525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d18449, d181525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d18450 q = 1) (hb : d180908 q = 1) : d181526 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d18450, d181526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d18450, d181526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro40926 (p : Pattern) (ha : d18456 p = 1) (hb : d180908 p = 1) : d181532 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18451 q = 1) (hb : d180908 q = 1) : d181527 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18451, d181527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40925 q ha hb
    | true =>
      simp only [d18451, d181527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d18452 q = 1) (hb : d180908 q = 1) : d181528 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18452, d181528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18452, d181528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18453 q = 1) (hb : d180908 q = 1) : d181529 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d18453, d181529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18453, d181529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18454 q = 1) (hb : d180908 q = 1) : d181530 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d18454, d181530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18454, d181530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d18455 q = 1) (hb : d180908 q = 1) : d181531 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d18455, d181531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18455, d181531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d18456 q = 1) (hb : d180908 q = 1) : d181532 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d18456, d181532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d18456, d181532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro40927 (p : Pattern) (ha : d129410 p = 1) (hb : d180908 p = 1) : d181538 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18385 q = 1) (hb : d180908 q = 1) : d181518 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d18385, d181518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40922 q ha hb
    | true =>
      simp only [d18385, d181518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40923 q ha hb
  have h2 (q : Pattern) (ha : d129406 q = 1) (hb : d180908 q = 1) : d181519 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d129406, d181519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129406, d181519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d18457 q = 1) (hb : d180908 q = 1) : d181533 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d18457, d181533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40926 q ha hb
    | true =>
      simp only [d18457, d181533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18458 q = 1) (hb : d180908 q = 1) : d181534 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d18458, d181534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18458, d181534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d129407 q = 1) (hb : d180908 q = 1) : d181535 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d129407, d181535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129407, d181535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129408 q = 1) (hb : d180908 q = 1) : d181536 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d129408, d181536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129408, d181536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d129409 q = 1) (hb : d180908 q = 1) : d181537 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d129409, d181537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129409, d181537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d129410 q = 1) (hb : d180908 q = 1) : d181538 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d129410, d181538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129410, d181538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro40928 (p : Pattern) (ha : d129416 p = 1) (hb : d180908 p = 1) : d181555 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129411 q = 1) (hb : d180908 q = 1) : d181539 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d129411, d181539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129411, d181539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40927 q ha hb
  have h2 (q : Pattern) (ha : d18474 q = 1) (hb : d180908 q = 1) : d181550 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d18474, d181550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18474, d181550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40915 q ha hb
  have h3 (q : Pattern) (ha : d129412 q = 1) (hb : d180908 q = 1) : d181551 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d129412, d181551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129412, d181551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d129413 q = 1) (hb : d180908 q = 1) : d181552 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d129413, d181552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129413, d181552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d129414 q = 1) (hb : d180908 q = 1) : d181553 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d129414, d181553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129414, d181553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d129415 q = 1) (hb : d180908 q = 1) : d181554 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d129415, d181554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129415, d181554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d129416 q = 1) (hb : d180908 q = 1) : d181555 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d129416, d181555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129416, d181555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro40929 (p : Pattern) (ha : d129422 p = 1) (hb : d180908 p = 1) : d181561 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129417 q = 1) (hb : d180908 q = 1) : d181556 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d129417, d181556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129417, d181556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40928 q ha hb
  have h2 (q : Pattern) (ha : d129418 q = 1) (hb : d180908 q = 1) : d181557 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d129418, d181557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129418, d181557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d129419 q = 1) (hb : d180908 q = 1) : d181558 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d129419, d181558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129419, d181558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d129420 q = 1) (hb : d180908 q = 1) : d181559 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d129420, d181559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129420, d181559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129421 q = 1) (hb : d180908 q = 1) : d181560 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d129421, d181560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129421, d181560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129422 q = 1) (hb : d180908 q = 1) : d181561 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d129422, d181561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129422, d181561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro40930 (p : Pattern) (ha : d129428 p = 1) (hb : d180908 p = 1) : d181567 p = 1 := by
  have h0 (q : Pattern) (ha : d129345 q = 1) (hb : d180908 q = 1) : d181096 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d129345, d181096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40843 q ha hb
    | true =>
      simp only [d129345, d181096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40856 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d129363 q = 1) (hb : d180908 q = 1) : d181185 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d129363, d181185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129363, d181185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40872 q ha hb
  have h3 (q : Pattern) (ha : d129364 q = 1) (hb : d180908 q = 1) : d181186 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d129364, d181186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129364, d181186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d129382 q = 1) (hb : d180908 q = 1) : d181310 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d129382, d181310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129382, d181310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40891 q ha hb
  have h5 (q : Pattern) (ha : d129383 q = 1) (hb : d180908 q = 1) : d181311 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d129383, d181311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129383, d181311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129384 q = 1) (hb : d180908 q = 1) : d181312 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d129384, d181312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129384, d181312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d129402 q = 1) (hb : d180908 q = 1) : d181438 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d129402, d181438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129402, d181438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40910 q ha hb
  have h8 (q : Pattern) (ha : d129403 q = 1) (hb : d180908 q = 1) : d181439 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d129403, d181439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129403, d181439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d129404 q = 1) (hb : d180908 q = 1) : d181440 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d129404, d181440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129404, d181440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d129405 q = 1) (hb : d180908 q = 1) : d181441 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d129405, d181441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d129405, d181441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d129423 q = 1) (hb : d180908 q = 1) : d181562 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d129423, d181562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129423, d181562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40929 q ha hb
  have h12 (q : Pattern) (ha : d129424 q = 1) (hb : d180908 q = 1) : d181563 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d129424, d181563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129424, d181563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d129425 q = 1) (hb : d180908 q = 1) : d181564 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d129425, d181564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129425, d181564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d129426 q = 1) (hb : d180908 q = 1) : d181565 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d129426, d181565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129426, d181565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d129427 q = 1) (hb : d180908 q = 1) : d181566 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d129427, d181566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d129427, d181566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d129428 q = 1) (hb : d180908 q = 1) : d181567 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d129428, d181567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d129428, d181567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro40931 (p : Pattern) (ha : d129434 p = 1) (hb : d180908 p = 1) : d181573 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129429 q = 1) (hb : d180908 q = 1) : d181568 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d129429, d181568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40930 q ha hb
    | true =>
      simp only [d129429, d181568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d129430 q = 1) (hb : d180908 q = 1) : d181569 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d129430, d181569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129430, d181569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d129431 q = 1) (hb : d180908 q = 1) : d181570 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d129431, d181570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129431, d181570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d129432 q = 1) (hb : d180908 q = 1) : d181571 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d129432, d181571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129432, d181571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d129433 q = 1) (hb : d180908 q = 1) : d181572 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d129433, d181572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129433, d181572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d129434 q = 1) (hb : d180908 q = 1) : d181573 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d129434, d181573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129434, d181573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro40932 (p : Pattern) (ha : d129440 p = 1) (hb : d180908 p = 1) : d181579 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129435 q = 1) (hb : d180908 q = 1) : d181574 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d129435, d181574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40931 q ha hb
    | true =>
      simp only [d129435, d181574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d129436 q = 1) (hb : d180908 q = 1) : d181575 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d129436, d181575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129436, d181575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d129437 q = 1) (hb : d180908 q = 1) : d181576 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d129437, d181576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129437, d181576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d129438 q = 1) (hb : d180908 q = 1) : d181577 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d129438, d181577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129438, d181577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d129439 q = 1) (hb : d180908 q = 1) : d181578 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d129439, d181578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129439, d181578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d129440 q = 1) (hb : d180908 q = 1) : d181579 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d129440, d181579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129440, d181579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro40933 (p : Pattern) (ha : d129446 p = 1) (hb : d180908 p = 1) : d181585 p = 1 := by
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
  have h5 (q : Pattern) (ha : d129445 q = 1) (hb : d180908 q = 1) : d181584 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d129445, d181584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129445, d181584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d129446 q = 1) (hb : d180908 q = 1) : d181585 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d129446, d181585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129446, d181585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro40934 (p : Pattern) (ha : d129452 p = 1) (hb : d180908 p = 1) : d181591 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129447 q = 1) (hb : d180908 q = 1) : d181586 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d129447, d181586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40933 q ha hb
    | true =>
      simp only [d129447, d181586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d129448 q = 1) (hb : d180908 q = 1) : d181587 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d129448, d181587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129448, d181587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d129449 q = 1) (hb : d180908 q = 1) : d181588 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d129449, d181588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129449, d181588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d129450 q = 1) (hb : d180908 q = 1) : d181589 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d129450, d181589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129450, d181589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d129451 q = 1) (hb : d180908 q = 1) : d181590 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d129451, d181590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129451, d181590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d129452 q = 1) (hb : d180908 q = 1) : d181591 q = 1 := by
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
theorem andIntro40935 (p : Pattern) (ha : d129458 p = 1) (hb : d180908 p = 1) : d181597 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129453 q = 1) (hb : d180908 q = 1) : d181592 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d129453, d181592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40934 q ha hb
    | true =>
      simp only [d129453, d181592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d129454 q = 1) (hb : d180908 q = 1) : d181593 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d129454, d181593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129454, d181593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d129455 q = 1) (hb : d180908 q = 1) : d181594 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d129455, d181594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129455, d181594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d129456 q = 1) (hb : d180908 q = 1) : d181595 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d129456, d181595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129456, d181595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d129457 q = 1) (hb : d180908 q = 1) : d181596 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d129457, d181596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129457, d181596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d129458 q = 1) (hb : d180908 q = 1) : d181597 q = 1 := by
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
theorem andIntro40936 (p : Pattern) (ha : d129464 p = 1) (hb : d180908 p = 1) : d181603 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129459 q = 1) (hb : d180908 q = 1) : d181598 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d129459, d181598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40935 q ha hb
    | true =>
      simp only [d129459, d181598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d129460 q = 1) (hb : d180908 q = 1) : d181599 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d129460, d181599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129460, d181599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d129461 q = 1) (hb : d180908 q = 1) : d181600 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d129461, d181600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129461, d181600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d129462 q = 1) (hb : d180908 q = 1) : d181601 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d129462, d181601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129462, d181601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d129463 q = 1) (hb : d180908 q = 1) : d181602 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d129463, d181602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129463, d181602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d129464 q = 1) (hb : d180908 q = 1) : d181603 q = 1 := by
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
theorem andIntro40937 (p : Pattern) (ha : d129470 p = 1) (hb : d180908 p = 1) : d181609 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129465 q = 1) (hb : d180908 q = 1) : d181604 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d129465, d181604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40936 q ha hb
    | true =>
      simp only [d129465, d181604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d129466 q = 1) (hb : d180908 q = 1) : d181605 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d129466, d181605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129466, d181605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d129467 q = 1) (hb : d180908 q = 1) : d181606 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d129467, d181606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129467, d181606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d129468 q = 1) (hb : d180908 q = 1) : d181607 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d129468, d181607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129468, d181607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d129469 q = 1) (hb : d180908 q = 1) : d181608 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d129469, d181608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129469, d181608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d129470 q = 1) (hb : d180908 q = 1) : d181609 q = 1 := by
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
theorem andIntro40938 (p : Pattern) (ha : d131104 p = 1) (hb : d180912 p = 1) : d0 p = 1 := by
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
  have h2 (q : Pattern) (ha : d18534 q = 1) (hb : d131100 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d18534, d131100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d18534, d131100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d51878 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d131101 q = 1) (hb : d180909 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d131101, d180909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d131101, d180909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d131102 q = 1) (hb : d180910 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d131102, d180910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131102, d180910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d131103 q = 1) (hb : d180911 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d131103, d180911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131103, d180911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d131104 q = 1) (hb : d180912 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d131104, d180912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d131104, d180912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro40939 (p : Pattern) (ha : d131114 p = 1) (hb : d180918 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131105 q = 1) (hb : d180913 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d131105, d180913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40938 q ha hb
    | true =>
      simp only [d131105, d180913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d131106 q = 1) (hb : d180914 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d131106, d180914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131106, d180914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d131107 q = 1) (hb : d180915 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d131107, d180915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131107, d180915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d131108 q = 1) (hb : d180916 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d131108, d180916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131108, d180916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d131109 q = 1) (hb : d180917 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d131109, d180917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131109, d180917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d131113 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d131114 q = 1) (hb : d180918 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d131114, d180918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131114, d180918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  exact h7 p ha hb
theorem andIntro40940 (p : Pattern) (ha : d131120 p = 1) (hb : d180924 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131115 q = 1) (hb : d180919 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d131115, d180919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40939 q ha hb
    | true =>
      simp only [d131115, d180919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d131116 q = 1) (hb : d180920 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d131116, d180920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131116, d180920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d131117 q = 1) (hb : d180921 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d131117, d180921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d131117, d180921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d131118 q = 1) (hb : d180922 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d131118, d180922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131118, d180922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d131119 q = 1) (hb : d180923 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d131119, d180923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131119, d180923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d131120 q = 1) (hb : d180924 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d131120, d180924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131120, d180924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro40941 (p : Pattern) (ha : d131126 p = 1) (hb : d180930 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131121 q = 1) (hb : d180925 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d131121, d180925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40940 q ha hb
    | true =>
      simp only [d131121, d180925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d131122 q = 1) (hb : d180926 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d131122, d180926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d131122, d180926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d131123 q = 1) (hb : d180927 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d131123, d180927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d131123, d180927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d131124 q = 1) (hb : d180928 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d131124, d180928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131124, d180928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d131125 q = 1) (hb : d180929 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d131125, d180929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131125, d180929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d131126 q = 1) (hb : d180930 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d131126, d180930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131126, d180930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro40942 (p : Pattern) (ha : d131132 p = 1) (hb : d180936 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131127 q = 1) (hb : d180931 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d131127, d180931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131127, d180931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40941 q ha hb
  have h2 (q : Pattern) (ha : d131128 q = 1) (hb : d180932 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d131128, d180932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d131128, d180932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d131129 q = 1) (hb : d180933 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d131129, d180933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d131129, d180933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d131130 q = 1) (hb : d180934 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d131130, d180934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131130, d180934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d131131 q = 1) (hb : d180935 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d131131, d180935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131131, d180935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d131132 q = 1) (hb : d180936 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d131132, d180936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131132, d180936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro40943 (p : Pattern) (ha : d131141 p = 1) (hb : d180944 p = 1) : d0 p = 1 := by
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
  have h2 (q : Pattern) (ha : d18571 q = 1) (hb : d131137 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d18571, d131137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d18571, d131137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d51991 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d131138 q = 1) (hb : d180941 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d131138, d180941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d131138, d180941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d131139 q = 1) (hb : d180942 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d131139, d180942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131139, d180942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d66 q = 1) (hb : d51918 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d66, d51918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d66, d51918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2 q ha hb
  have h7 (q : Pattern) (ha : d18534 q = 1) (hb : d131100 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d18534, d131100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d18534, d131100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d51878 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d131101 q = 1) (hb : d180909 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d131101, d180909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d131101, d180909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d131102 q = 1) (hb : d180910 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d131102, d180910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d131102, d180910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d131140 q = 1) (hb : d180943 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d131140, d180943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131140, d180943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d131103 q = 1) (hb : d180911 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d131103, d180911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d131103, d180911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d131141 q = 1) (hb : d180944 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d131141, d180944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d131141, d180944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro40944 (p : Pattern) (ha : d131151 p = 1) (hb : d180950 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131142 q = 1) (hb : d180945 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d131142, d180945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40943 q ha hb
    | true =>
      simp only [d131142, d180945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40938 q ha hb
  have h2 (q : Pattern) (ha : d131143 q = 1) (hb : d180946 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d131143, d180946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131143, d180946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d131144 q = 1) (hb : d180947 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d131144, d180947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131144, d180947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d131105 q = 1) (hb : d180913 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d131105, d180913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40938 q ha hb
    | true =>
      simp only [d131105, d180913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d131106 q = 1) (hb : d180914 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d131106, d180914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131106, d180914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d131107 q = 1) (hb : d180915 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d131107, d180915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131107, d180915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d131145 q = 1) (hb : d180948 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d131145, d180948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131145, d180948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d131108 q = 1) (hb : d180916 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d131108, d180916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d131108, d180916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d131146 q = 1) (hb : d180949 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d131146, d180949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d131146, d180949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d131150 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d131151 q = 1) (hb : d180950 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d131151, d180950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d131151, d180950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro40945 (p : Pattern) (ha : d131157 p = 1) (hb : d180956 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131152 q = 1) (hb : d180951 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d131152, d180951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40944 q ha hb
    | true =>
      simp only [d131152, d180951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d131153 q = 1) (hb : d180952 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d131153, d180952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131153, d180952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d131115 q = 1) (hb : d180919 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d131115, d180919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40939 q ha hb
    | true =>
      simp only [d131115, d180919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d131116 q = 1) (hb : d180920 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d131116, d180920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131116, d180920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d131154 q = 1) (hb : d180953 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d131154, d180953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d131154, d180953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d131155 q = 1) (hb : d180954 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d131155, d180954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131155, d180954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d131156 q = 1) (hb : d180955 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d131156, d180955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d131156, d180955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d131157 q = 1) (hb : d180956 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d131157, d180956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d131157, d180956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro40946 (p : Pattern) (ha : d131163 p = 1) (hb : d180962 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131158 q = 1) (hb : d180957 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d131158, d180957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40945 q ha hb
    | true =>
      simp only [d131158, d180957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40940 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d131121 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d131159 q = 1) (hb : d180958 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d131159, d180958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d131159, d180958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d131121 q = 1) (hb : d180925 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d131121, d180925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40940 q ha hb
    | true =>
      simp only [d131121, d180925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d131122 q = 1) (hb : d180926 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d131122, d180926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131122, d180926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d131160 q = 1) (hb : d180959 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d131160, d180959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131160, d180959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d131161 q = 1) (hb : d180960 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d131161, d180960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131161, d180960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d131162 q = 1) (hb : d180961 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d131162, d180961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131162, d180961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d131163 q = 1) (hb : d180962 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d131163, d180962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131163, d180962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro40947 (p : Pattern) (ha : d131169 p = 1) (hb : d180968 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131164 q = 1) (hb : d180963 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d131164, d180963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131164, d180963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40946 q ha hb
  have h2 (q : Pattern) (ha : d131165 q = 1) (hb : d180964 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d131165, d180964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d131165, d180964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d131166 q = 1) (hb : d180965 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d131166, d180965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d131166, d180965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d131167 q = 1) (hb : d180966 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d131167, d180966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131167, d180966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d131168 q = 1) (hb : d180967 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d131168, d180967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131168, d180967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d131169 q = 1) (hb : d180968 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d131169, d180968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131169, d180968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro40948 (p : Pattern) (ha : d131183 p = 1) (hb : d180980 p = 1) : d0 p = 1 := by
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
  have h2 (q : Pattern) (ha : d18631 q = 1) (hb : d131175 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d18631, d131175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d18631, d131175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52119 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d131176 q = 1) (hb : d180974 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d131176, d180974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d131176, d180974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d131177 q = 1) (hb : d180975 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d131177, d180975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131177, d180975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d226 q = 1) (hb : d52044 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d226, d52044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d226, d52044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19 q ha hb
  have h7 (q : Pattern) (ha : d18571 q = 1) (hb : d131137 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d18571, d131137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d18571, d131137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d51991 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d131138 q = 1) (hb : d180941 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d131138, d180941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d131138, d180941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d131139 q = 1) (hb : d180942 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d131139, d180942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d131139, d180942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d131178 q = 1) (hb : d180976 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d131178, d180976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131178, d180976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d12599 q = 1) (hb : d113007 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d12599, d113007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12599, d113007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23261 q ha hb
  have h13 (q : Pattern) (ha : d18635 q = 1) (hb : d131179 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d18635, d131179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d18635, d131179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d101017 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d131180 q = 1) (hb : d180977 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d131180, d180977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d131180, d180977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d131181 q = 1) (hb : d180978 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d131181, d180978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d131181, d180978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h17 (q : Pattern) (ha : d66 q = 1) (hb : d51918 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d66, d51918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d66, d51918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2 q ha hb
  have h18 (q : Pattern) (ha : d18534 q = 1) (hb : d131100 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d18534, d131100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d18534, d131100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d0 q = 1) (hb : d51878 q = 1) : d0 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d131101 q = 1) (hb : d180909 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d131101, d180909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
    | true =>
      simp only [d131101, d180909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
  have h21 (q : Pattern) (ha : d131102 q = 1) (hb : d180910 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d131102, d180910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d131102, d180910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d131182 q = 1) (hb : d180979 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d131182, d180979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d131182, d180979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d131183 q = 1) (hb : d180980 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d131183, d180980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d131183, d180980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro40949 (p : Pattern) (ha : d131193 p = 1) (hb : d180986 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131184 q = 1) (hb : d180981 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d131184, d180981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40948 q ha hb
    | true =>
      simp only [d131184, d180981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40943 q ha hb
  have h2 (q : Pattern) (ha : d131185 q = 1) (hb : d180982 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d131185, d180982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131185, d180982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d131186 q = 1) (hb : d180983 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d131186, d180983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131186, d180983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d131142 q = 1) (hb : d180945 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d131142, d180945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40943 q ha hb
    | true =>
      simp only [d131142, d180945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40938 q ha hb
  have h5 (q : Pattern) (ha : d131143 q = 1) (hb : d180946 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d131143, d180946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131143, d180946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d131144 q = 1) (hb : d180947 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d131144, d180947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131144, d180947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d131187 q = 1) (hb : d180984 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d131187, d180984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131187, d180984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d131105 q = 1) (hb : d180913 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d131105, d180913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40938 q ha hb
    | true =>
      simp only [d131105, d180913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d131106 q = 1) (hb : d180914 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d131106, d180914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131106, d180914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d131107 q = 1) (hb : d180915 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d131107, d180915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131107, d180915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d131145 q = 1) (hb : d180948 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d131145, d180948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d131145, d180948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d131188 q = 1) (hb : d180985 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d131188, d180985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d131188, d180985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d131192 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d131193 q = 1) (hb : d180986 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d131193, d180986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d131193, d180986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  exact h14 p ha hb
theorem andIntro40950 (p : Pattern) (ha : d131199 p = 1) (hb : d180992 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131194 q = 1) (hb : d180987 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d131194, d180987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40949 q ha hb
    | true =>
      simp only [d131194, d180987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d131195 q = 1) (hb : d180988 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d131195, d180988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131195, d180988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d131152 q = 1) (hb : d180951 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d131152, d180951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40944 q ha hb
    | true =>
      simp only [d131152, d180951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d131153 q = 1) (hb : d180952 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d131153, d180952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131153, d180952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d131196 q = 1) (hb : d180989 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d131196, d180989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d131196, d180989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d131197 q = 1) (hb : d180990 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d131197, d180990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131197, d180990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d131198 q = 1) (hb : d180991 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d131198, d180991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d131198, d180991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d131199 q = 1) (hb : d180992 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d131199, d180992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d131199, d180992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro40951 (p : Pattern) (ha : d131205 p = 1) (hb : d180998 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131152 q = 1) (hb : d180951 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d131152, d180951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40944 q ha hb
    | true =>
      simp only [d131152, d180951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d131153 q = 1) (hb : d180952 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d131153, d180952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131153, d180952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d131202 q = 1) (hb : d180995 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d131202, d180995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d131202, d180995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d131203 q = 1) (hb : d180996 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d131203, d180996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131203, d180996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d131204 q = 1) (hb : d180997 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d131204, d180997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131204, d180997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d131205 q = 1) (hb : d180998 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d131205, d180998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131205, d180998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro40952 (p : Pattern) (ha : d131211 p = 1) (hb : d181004 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131200 q = 1) (hb : d180993 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d131200, d180993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40950 q ha hb
    | true =>
      simp only [d131200, d180993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40945 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d131158 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d131201 q = 1) (hb : d180994 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d131201, d180994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d131201, d180994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d131206 q = 1) (hb : d180999 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d131206, d180999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40951 q ha hb
    | true =>
      simp only [d131206, d180999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d131207 q = 1) (hb : d181000 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d131207, d181000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131207, d181000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d131208 q = 1) (hb : d181001 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d131208, d181001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131208, d181001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d131209 q = 1) (hb : d181002 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d131209, d181002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131209, d181002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d131210 q = 1) (hb : d181003 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d131210, d181003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131210, d181003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d131211 q = 1) (hb : d181004 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d131211, d181004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131211, d181004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro40953 (p : Pattern) (ha : d131217 p = 1) (hb : d181010 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131121 q = 1) (hb : d180925 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d131121, d180925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40940 q ha hb
    | true =>
      simp only [d131121, d180925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d131213 q = 1) (hb : d181006 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d131213, d181006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131213, d181006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d131214 q = 1) (hb : d181007 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d131214, d181007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d131214, d181007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d131215 q = 1) (hb : d181008 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d131215, d181008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131215, d181008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d131216 q = 1) (hb : d181009 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d131216, d181009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131216, d181009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d131217 q = 1) (hb : d181010 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d131217, d181010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131217, d181010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro40954 (p : Pattern) (ha : d131223 p = 1) (hb : d181016 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131212 q = 1) (hb : d181005 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d131212, d181005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131212, d181005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40952 q ha hb
  have h2 (q : Pattern) (ha : d131218 q = 1) (hb : d181011 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d131218, d181011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131218, d181011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40953 q ha hb
  have h3 (q : Pattern) (ha : d131219 q = 1) (hb : d181012 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d131219, d181012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d131219, d181012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d131220 q = 1) (hb : d181013 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d131220, d181013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131220, d181013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d131221 q = 1) (hb : d181014 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d131221, d181014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131221, d181014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d131222 q = 1) (hb : d181015 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d131222, d181015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131222, d181015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d131223 q = 1) (hb : d181016 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d131223, d181016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131223, d181016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro40955 (p : Pattern) (ha : d131229 p = 1) (hb : d181022 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131133 q = 1) (hb : d180937 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d131133, d180937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131133, d180937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40942 q ha hb
  have h2 (q : Pattern) (ha : d131134 q = 1) (hb : d180938 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d131134, d180938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131134, d180938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d131135 q = 1) (hb : d180939 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d131135, d180939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131135, d180939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d131136 q = 1) (hb : d180940 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d131136, d180940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131136, d180940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d131170 q = 1) (hb : d180969 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d131170, d180969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131170, d180969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40947 q ha hb
  have h6 (q : Pattern) (ha : d131171 q = 1) (hb : d180970 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d131171, d180970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131171, d180970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d131172 q = 1) (hb : d180971 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d131172, d180971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131172, d180971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d131173 q = 1) (hb : d180972 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d131173, d180972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131173, d180972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d131174 q = 1) (hb : d180973 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d131174, d180973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131174, d180973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d131224 q = 1) (hb : d181017 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d131224, d181017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131224, d181017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40954 q ha hb
  have h11 (q : Pattern) (ha : d131225 q = 1) (hb : d181018 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d131225, d181018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131225, d181018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d131226 q = 1) (hb : d181019 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d131226, d181019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131226, d181019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d131227 q = 1) (hb : d181020 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d131227, d181020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131227, d181020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d131228 q = 1) (hb : d181021 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d131228, d181021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131228, d181021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d131229 q = 1) (hb : d181022 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d131229, d181022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d131229, d181022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro40956 (p : Pattern) (ha : d131241 p = 1) (hb : d181031 p = 1) : d0 p = 1 := by
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
  have h2 (q : Pattern) (ha : d18708 q = 1) (hb : d131230 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d18708, d131230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d18708, d131230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52291 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d131231 q = 1) (hb : d181023 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d131231, d181023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d131231, d181023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d131232 q = 1) (hb : d181024 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d131232, d181024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131232, d181024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d16156 q = 1) (hb : d127047 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d16156, d127047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16156, d127047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23272 q ha hb
  have h7 (q : Pattern) (ha : d18711 q = 1) (hb : d131233 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d18711, d131233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d18711, d131233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d101075 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d131234 q = 1) (hb : d181025 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d131234, d181025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d131234, d181025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d131235 q = 1) (hb : d181026 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d131235, d181026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d131235, d181026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d131236 q = 1) (hb : d181027 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d131236, d181027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131236, d181027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d12858 q = 1) (hb : d113214 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d12858, d113214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12858, d113214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23273 q ha hb
  have h13 (q : Pattern) (ha : d18715 q = 1) (hb : d131237 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d18715, d131237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d18715, d131237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d101085 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d131238 q = 1) (hb : d181028 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d131238, d181028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d131238, d181028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d131239 q = 1) (hb : d181029 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d131239, d181029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d131239, d181029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h17 (q : Pattern) (ha : d12599 q = 1) (hb : d113007 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d12599, d113007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12599, d113007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23261 q ha hb
  have h18 (q : Pattern) (ha : d18635 q = 1) (hb : d131179 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d18635, d131179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d18635, d131179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d0 q = 1) (hb : d101017 q = 1) : d0 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d131180 q = 1) (hb : d180977 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d131180, d180977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
    | true =>
      simp only [d131180, d180977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
  have h21 (q : Pattern) (ha : d131181 q = 1) (hb : d180978 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d131181, d180978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d131181, d180978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d131240 q = 1) (hb : d181030 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d131240, d181030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d131240, d181030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d131241 q = 1) (hb : d181031 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d131241, d181031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d131241, d181031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro40957 (p : Pattern) (ha : d131245 p = 1) (hb : d181035 p = 1) : d0 p = 1 := by
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
  have h2 (q : Pattern) (ha : d18635 q = 1) (hb : d131179 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d18635, d131179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d18635, d131179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d101017 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d131180 q = 1) (hb : d180977 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d131180, d180977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d131180, d180977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d131181 q = 1) (hb : d180978 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d131181, d180978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131181, d180978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d66 q = 1) (hb : d51918 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d66, d51918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d66, d51918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2 q ha hb
  have h7 (q : Pattern) (ha : d18534 q = 1) (hb : d131100 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d18534, d131100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d18534, d131100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d51878 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d131101 q = 1) (hb : d180909 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d131101, d180909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d131101, d180909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d131102 q = 1) (hb : d180910 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d131102, d180910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d131102, d180910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d131182 q = 1) (hb : d180979 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d131182, d180979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131182, d180979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d131103 q = 1) (hb : d180911 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d131103, d180911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d131103, d180911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d131245 q = 1) (hb : d181035 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d131245, d181035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d131245, d181035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro40958 (p : Pattern) (ha : d131257 p = 1) (hb : d181041 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131242 q = 1) (hb : d181032 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d131242, d181032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40956 q ha hb
    | true =>
      simp only [d131242, d181032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40948 q ha hb
  have h2 (q : Pattern) (ha : d131243 q = 1) (hb : d181033 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d131243, d181033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131243, d181033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d131244 q = 1) (hb : d181034 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d131244, d181034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131244, d181034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d131246 q = 1) (hb : d181036 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d131246, d181036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40948 q ha hb
    | true =>
      simp only [d131246, d181036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40957 q ha hb
  have h5 (q : Pattern) (ha : d131247 q = 1) (hb : d181037 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d131247, d181037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131247, d181037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d131248 q = 1) (hb : d181038 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d131248, d181038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131248, d181038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d131249 q = 1) (hb : d181039 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d131249, d181039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131249, d181039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d131184 q = 1) (hb : d180981 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d131184, d180981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40948 q ha hb
    | true =>
      simp only [d131184, d180981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40943 q ha hb
  have h9 (q : Pattern) (ha : d131185 q = 1) (hb : d180982 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d131185, d180982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131185, d180982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d131186 q = 1) (hb : d180983 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d131186, d180983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131186, d180983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d131142 q = 1) (hb : d180945 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d131142, d180945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40943 q ha hb
    | true =>
      simp only [d131142, d180945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40938 q ha hb
  have h12 (q : Pattern) (ha : d131143 q = 1) (hb : d180946 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d131143, d180946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131143, d180946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d131144 q = 1) (hb : d180947 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d131144, d180947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131144, d180947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d131187 q = 1) (hb : d180984 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d131187, d180984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d131187, d180984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d131250 q = 1) (hb : d181040 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d131250, d181040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d131250, d181040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d0 q = 1) (hb : d131256 q = 1) : d0 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d131257 q = 1) (hb : d181041 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d131257, d181041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d131257, d181041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q hb ha
  exact h17 p ha hb
theorem andIntro40959 (p : Pattern) (ha : d131264 p = 1) (hb : d181046 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131184 q = 1) (hb : d180981 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d131184, d180981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40948 q ha hb
    | true =>
      simp only [d131184, d180981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40943 q ha hb
  have h2 (q : Pattern) (ha : d131185 q = 1) (hb : d180982 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d131185, d180982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131185, d180982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d131186 q = 1) (hb : d180983 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d131186, d180983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131186, d180983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d131142 q = 1) (hb : d180945 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d131142, d180945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40943 q ha hb
    | true =>
      simp only [d131142, d180945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40938 q ha hb
  have h5 (q : Pattern) (ha : d131143 q = 1) (hb : d180946 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d131143, d180946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131143, d180946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d131144 q = 1) (hb : d180947 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d131144, d180947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131144, d180947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d131187 q = 1) (hb : d180984 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d131187, d180984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131187, d180984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d131260 q = 1) (hb : d181044 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d131260, d181044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d131260, d181044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d131261 q = 1) (hb : d181045 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d131261, d181045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d131261, d181045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d131263 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d131264 q = 1) (hb : d181046 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d131264, d181046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d131264, d181046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro40960 (p : Pattern) (ha : d131270 p = 1) (hb : d181052 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131258 q = 1) (hb : d181042 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d131258, d181042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40958 q ha hb
    | true =>
      simp only [d131258, d181042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d131259 q = 1) (hb : d181043 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d131259, d181043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131259, d181043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d131265 q = 1) (hb : d181047 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d131265, d181047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40959 q ha hb
    | true =>
      simp only [d131265, d181047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d131266 q = 1) (hb : d181048 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d131266, d181048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131266, d181048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d131267 q = 1) (hb : d181049 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d131267, d181049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d131267, d181049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d131268 q = 1) (hb : d181050 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d131268, d181050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131268, d181050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d131269 q = 1) (hb : d181051 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d131269, d181051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d131269, d181051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d131270 q = 1) (hb : d181052 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d131270, d181052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d131270, d181052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro40961 (p : Pattern) (ha : d131273 p = 1) (hb : d181054 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131142 q = 1) (hb : d180945 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d131142, d180945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40943 q ha hb
    | true =>
      simp only [d131142, d180945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40938 q ha hb
  have h2 (q : Pattern) (ha : d131143 q = 1) (hb : d180946 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d131143, d180946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131143, d180946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d131144 q = 1) (hb : d180947 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d131144, d180947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131144, d180947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d131260 q = 1) (hb : d181044 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d131260, d181044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131260, d181044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d131271 q = 1) (hb : d181053 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d131271, d181053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131271, d181053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d131272 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d131273 q = 1) (hb : d181054 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d131273, d181054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131273, d181054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  exact h7 p ha hb
theorem andIntro40962 (p : Pattern) (ha : d131279 p = 1) (hb : d181060 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131265 q = 1) (hb : d181047 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d131265, d181047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40959 q ha hb
    | true =>
      simp only [d131265, d181047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d131266 q = 1) (hb : d181048 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d131266, d181048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131266, d181048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d131274 q = 1) (hb : d181055 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d131274, d181055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40961 q ha hb
    | true =>
      simp only [d131274, d181055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d131275 q = 1) (hb : d181056 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d131275, d181056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131275, d181056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d131276 q = 1) (hb : d181057 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d131276, d181057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d131276, d181057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d131277 q = 1) (hb : d181058 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d131277, d181058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131277, d181058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d131278 q = 1) (hb : d181059 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d131278, d181059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d131278, d181059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d131279 q = 1) (hb : d181060 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d131279, d181060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d131279, d181060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro40963 (p : Pattern) (ha : d131290 p = 1) (hb : d181066 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131265 q = 1) (hb : d181047 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d131265, d181047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40959 q ha hb
    | true =>
      simp only [d131265, d181047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d131266 q = 1) (hb : d181048 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d131266, d181048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131266, d181048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d131287 q = 1) (hb : d181063 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d131287, d181063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d131287, d181063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d131288 q = 1) (hb : d181064 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d131288, d181064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131288, d181064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d131289 q = 1) (hb : d181065 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d131289, d181065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131289, d181065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d131290 q = 1) (hb : d181066 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d131290, d181066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131290, d181066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro40964 (p : Pattern) (ha : d131296 p = 1) (hb : d181072 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131280 q = 1) (hb : d181061 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d131280, d181061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40960 q ha hb
    | true =>
      simp only [d131280, d181061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40962 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d131285 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d131286 q = 1) (hb : d181062 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d131286, d181062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d131286, d181062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d131291 q = 1) (hb : d181067 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d131291, d181067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40963 q ha hb
    | true =>
      simp only [d131291, d181067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d131292 q = 1) (hb : d181068 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d131292, d181068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131292, d181068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d131293 q = 1) (hb : d181069 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d131293, d181069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131293, d181069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d131294 q = 1) (hb : d181070 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d131294, d181070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131294, d181070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d131295 q = 1) (hb : d181071 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d131295, d181071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131295, d181071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d131296 q = 1) (hb : d181072 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d131296, d181072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131296, d181072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro40965 (p : Pattern) (ha : d131284 p = 1) (hb : d181077 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131274 q = 1) (hb : d181055 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d131274, d181055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40961 q ha hb
    | true =>
      simp only [d131274, d181055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d131275 q = 1) (hb : d181056 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d131275, d181056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131275, d181056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d131281 q = 1) (hb : d181074 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d131281, d181074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d131281, d181074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d131282 q = 1) (hb : d181075 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d131282, d181075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131282, d181075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d131283 q = 1) (hb : d181076 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d131283, d181076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131283, d181076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d131284 q = 1) (hb : d181077 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d131284, d181077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131284, d181077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro40966 (p : Pattern) (ha : d131303 p = 1) (hb : d181083 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131298 q = 1) (hb : d181078 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d131298, d181078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40965 q ha hb
    | true =>
      simp only [d131298, d181078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d131299 q = 1) (hb : d181079 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d131299, d181079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131299, d181079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d131300 q = 1) (hb : d181080 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d131300, d181080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d131300, d181080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d131301 q = 1) (hb : d181081 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d131301, d181081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131301, d181081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d131302 q = 1) (hb : d181082 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d131302, d181082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131302, d181082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d131303 q = 1) (hb : d181083 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d131303, d181083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131303, d181083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro40967 (p : Pattern) (ha : d131309 p = 1) (hb : d181089 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131297 q = 1) (hb : d181073 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d131297, d181073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131297, d181073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40964 q ha hb
  have h2 (q : Pattern) (ha : d131304 q = 1) (hb : d181084 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d131304, d181084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131304, d181084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40966 q ha hb
  have h3 (q : Pattern) (ha : d131305 q = 1) (hb : d181085 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d131305, d181085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d131305, d181085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d131306 q = 1) (hb : d181086 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d131306, d181086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131306, d181086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d131307 q = 1) (hb : d181087 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d131307, d181087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131307, d181087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d131308 q = 1) (hb : d181088 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d131308, d181088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131308, d181088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d131309 q = 1) (hb : d181089 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d131309, d181089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131309, d181089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro40968 (p : Pattern) (ha : d131315 p = 1) (hb : d181095 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131310 q = 1) (hb : d181090 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d131310, d181090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131310, d181090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40967 q ha hb
  have h2 (q : Pattern) (ha : d131311 q = 1) (hb : d181091 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d131311, d181091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131311, d181091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d131312 q = 1) (hb : d181092 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d131312, d181092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131312, d181092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d131313 q = 1) (hb : d181093 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d131313, d181093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131313, d181093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d131314 q = 1) (hb : d181094 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d131314, d181094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131314, d181094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d131315 q = 1) (hb : d181095 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d131315, d181095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131315, d181095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro40969 (p : Pattern) (ha : d131328 p = 1) (hb : d181105 p = 1) : d0 p = 1 := by
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
  have h2 (q : Pattern) (ha : d18831 q = 1) (hb : d131317 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d18831, d131317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d18831, d131317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52512 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d131318 q = 1) (hb : d181097 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d131318, d181097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d131318, d181097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d131319 q = 1) (hb : d181098 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d131319, d181098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131319, d181098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d16356 q = 1) (hb : d127213 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d16356, d127213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16356, d127213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23290 q ha hb
  have h7 (q : Pattern) (ha : d18834 q = 1) (hb : d131320 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d18834, d131320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d18834, d131320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d101169 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d131321 q = 1) (hb : d181099 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d131321, d181099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d131321, d181099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d131322 q = 1) (hb : d181100 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d131322, d181100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d131322, d181100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d131323 q = 1) (hb : d181101 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d131323, d181101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131323, d181101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d14644 q = 1) (hb : d122847 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d14644, d122847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14644, d122847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23291 q ha hb
  have h13 (q : Pattern) (ha : d18838 q = 1) (hb : d131324 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d18838, d131324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d18838, d131324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d101179 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d131325 q = 1) (hb : d181102 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d131325, d181102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d131325, d181102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d131326 q = 1) (hb : d181103 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d131326, d181103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d131326, d181103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h17 (q : Pattern) (ha : d12858 q = 1) (hb : d113214 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d12858, d113214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12858, d113214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23273 q ha hb
  have h18 (q : Pattern) (ha : d18715 q = 1) (hb : d131237 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d18715, d131237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d18715, d131237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d0 q = 1) (hb : d101085 q = 1) : d0 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d131238 q = 1) (hb : d181028 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d131238, d181028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
    | true =>
      simp only [d131238, d181028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
  have h21 (q : Pattern) (ha : d131239 q = 1) (hb : d181029 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d131239, d181029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d131239, d181029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d131327 q = 1) (hb : d181104 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d131327, d181104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d131327, d181104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d131328 q = 1) (hb : d181105 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d131328, d181105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d131328, d181105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro40970 (p : Pattern) (ha : d131333 p = 1) (hb : d181109 p = 1) : d0 p = 1 := by
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
  have h2 (q : Pattern) (ha : d18708 q = 1) (hb : d131230 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d18708, d131230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d18708, d131230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52291 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d131231 q = 1) (hb : d181023 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d131231, d181023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d131231, d181023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d131232 q = 1) (hb : d181024 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d131232, d181024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131232, d181024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d16156 q = 1) (hb : d127047 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d16156, d127047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16156, d127047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23272 q ha hb
  have h7 (q : Pattern) (ha : d18711 q = 1) (hb : d131233 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d18711, d131233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d18711, d131233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d101075 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d131234 q = 1) (hb : d181025 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d131234, d181025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d131234, d181025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d131235 q = 1) (hb : d181026 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d131235, d181026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d131235, d181026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d131236 q = 1) (hb : d181027 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d131236, d181027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131236, d181027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d12858 q = 1) (hb : d113214 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d12858, d113214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12858, d113214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23273 q ha hb
  have h13 (q : Pattern) (ha : d18715 q = 1) (hb : d131237 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d18715, d131237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d18715, d131237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d101085 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d131238 q = 1) (hb : d181028 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d131238, d181028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d131238, d181028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d131239 q = 1) (hb : d181029 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d131239, d181029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d131239, d181029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h17 (q : Pattern) (ha : d971 q = 1) (hb : d52590 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d971, d52590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d971, d52590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100 q ha hb
  have h18 (q : Pattern) (ha : d18843 q = 1) (hb : d131329 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d18843, d131329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d18843, d131329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d0 q = 1) (hb : d52429 q = 1) : d0 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d131330 q = 1) (hb : d181106 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d131330, d181106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
    | true =>
      simp only [d131330, d181106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
  have h21 (q : Pattern) (ha : d131331 q = 1) (hb : d181107 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d131331, d181107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d131331, d181107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d131332 q = 1) (hb : d181108 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d131332, d181108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d131332, d181108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d131333 q = 1) (hb : d181109 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d131333, d181109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d131333, d181109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro40971 (p : Pattern) (ha : d131338 p = 1) (hb : d181114 p = 1) : d0 p = 1 := by
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
  have h2 (q : Pattern) (ha : d18715 q = 1) (hb : d131237 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d18715, d131237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d18715, d131237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d101085 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d131238 q = 1) (hb : d181028 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d131238, d181028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d131238, d181028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d131239 q = 1) (hb : d181029 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d131239, d181029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131239, d181029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d971 q = 1) (hb : d52590 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d971, d52590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d971, d52590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100 q ha hb
  have h7 (q : Pattern) (ha : d18843 q = 1) (hb : d131329 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d18843, d131329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d18843, d131329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52429 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d131330 q = 1) (hb : d181106 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d131330, d181106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d131330, d181106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d131331 q = 1) (hb : d181107 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d131331, d181107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d131331, d181107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d131332 q = 1) (hb : d181108 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d131332, d181108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131332, d181108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d131337 q = 1) (hb : d181113 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d131337, d181113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d131337, d181113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d131338 q = 1) (hb : d181114 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d131338, d181114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d131338, d181114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro40972 (p : Pattern) (ha : d131344 p = 1) (hb : d181120 p = 1) : d0 p = 1 := by
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
  have h2 (q : Pattern) (ha : d18631 q = 1) (hb : d131175 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d18631, d131175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d18631, d131175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52119 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d131176 q = 1) (hb : d180974 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d131176, d180974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d131176, d180974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d131177 q = 1) (hb : d180975 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d131177, d180975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131177, d180975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d971 q = 1) (hb : d52590 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d971, d52590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d971, d52590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100 q ha hb
  have h7 (q : Pattern) (ha : d18843 q = 1) (hb : d131329 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d18843, d131329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d18843, d131329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52429 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d131330 q = 1) (hb : d181106 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d131330, d181106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d131330, d181106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d131331 q = 1) (hb : d181107 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d131331, d181107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d131331, d181107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d131343 q = 1) (hb : d181119 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d131343, d181119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131343, d181119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d131337 q = 1) (hb : d181113 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d131337, d181113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d131337, d181113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d131344 q = 1) (hb : d181120 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d131344, d181120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d131344, d181120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro40973 (p : Pattern) (ha : d131348 p = 1) (hb : d181124 p = 1) : d0 p = 1 := by
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
  have h2 (q : Pattern) (ha : d18843 q = 1) (hb : d131329 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d18843, d131329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d18843, d131329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52429 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d131330 q = 1) (hb : d181106 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d131330, d181106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d131330, d181106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d131331 q = 1) (hb : d181107 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d131331, d181107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131331, d181107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d131337 q = 1) (hb : d181113 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d131337, d181113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131337, d181113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d131348 q = 1) (hb : d181124 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d131348, d181124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d131348, d181124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro40974 (p : Pattern) (ha : d131365 p = 1) (hb : d181130 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131334 q = 1) (hb : d181110 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d131334, d181110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40969 q ha hb
    | true =>
      simp only [d131334, d181110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40970 q ha hb
  have h2 (q : Pattern) (ha : d131335 q = 1) (hb : d181111 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d131335, d181111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131335, d181111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d131336 q = 1) (hb : d181112 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d131336, d181112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131336, d181112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d131339 q = 1) (hb : d181115 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d131339, d181115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40970 q ha hb
    | true =>
      simp only [d131339, d181115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40971 q ha hb
  have h5 (q : Pattern) (ha : d131340 q = 1) (hb : d181116 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d131340, d181116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131340, d181116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d131341 q = 1) (hb : d181117 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d131341, d181117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131341, d181117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d131342 q = 1) (hb : d181118 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d131342, d181118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131342, d181118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d131345 q = 1) (hb : d181121 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d131345, d181121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40970 q ha hb
    | true =>
      simp only [d131345, d181121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40972 q ha hb
  have h9 (q : Pattern) (ha : d131346 q = 1) (hb : d181122 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d131346, d181122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131346, d181122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d131347 q = 1) (hb : d181123 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d131347, d181123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131347, d181123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d131349 q = 1) (hb : d181125 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d131349, d181125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40972 q ha hb
    | true =>
      simp only [d131349, d181125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40973 q ha hb
  have h12 (q : Pattern) (ha : d131350 q = 1) (hb : d181126 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d131350, d181126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131350, d181126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d131351 q = 1) (hb : d181127 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d131351, d181127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131351, d181127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d131352 q = 1) (hb : d181128 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d131352, d181128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d131352, d181128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d131353 q = 1) (hb : d181129 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d131353, d181129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d131353, d181129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d0 q = 1) (hb : d131364 q = 1) : d0 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d131365 q = 1) (hb : d181130 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d131365, d181130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d131365, d181130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q hb ha
  exact h17 p ha hb
theorem andIntro40975 (p : Pattern) (ha : d131372 p = 1) (hb : d181135 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131345 q = 1) (hb : d181121 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d131345, d181121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40970 q ha hb
    | true =>
      simp only [d131345, d181121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40972 q ha hb
  have h2 (q : Pattern) (ha : d131346 q = 1) (hb : d181122 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d131346, d181122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131346, d181122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d131347 q = 1) (hb : d181123 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d131347, d181123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131347, d181123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d131349 q = 1) (hb : d181125 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d131349, d181125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40972 q ha hb
    | true =>
      simp only [d131349, d181125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40973 q ha hb
  have h5 (q : Pattern) (ha : d131350 q = 1) (hb : d181126 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d131350, d181126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131350, d181126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d131351 q = 1) (hb : d181127 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d131351, d181127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131351, d181127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d131352 q = 1) (hb : d181128 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d131352, d181128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131352, d181128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d131368 q = 1) (hb : d181133 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d131368, d181133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d131368, d181133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d131369 q = 1) (hb : d181134 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d131369, d181134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d131369, d181134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d131371 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d131372 q = 1) (hb : d181135 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d131372, d181135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d131372, d181135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro40976 (p : Pattern) (ha : d131378 p = 1) (hb : d181141 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131366 q = 1) (hb : d181131 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d131366, d181131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40974 q ha hb
    | true =>
      simp only [d131366, d181131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d131367 q = 1) (hb : d181132 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d131367, d181132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131367, d181132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d131373 q = 1) (hb : d181136 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d131373, d181136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40975 q ha hb
    | true =>
      simp only [d131373, d181136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d131374 q = 1) (hb : d181137 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d131374, d181137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131374, d181137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d131375 q = 1) (hb : d181138 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d131375, d181138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d131375, d181138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d131376 q = 1) (hb : d181139 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d131376, d181139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131376, d181139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d131377 q = 1) (hb : d181140 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d131377, d181140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d131377, d181140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d131378 q = 1) (hb : d181141 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d131378, d181141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d131378, d181141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro40977 (p : Pattern) (ha : d131381 p = 1) (hb : d181143 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131349 q = 1) (hb : d181125 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d131349, d181125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40972 q ha hb
    | true =>
      simp only [d131349, d181125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40973 q ha hb
  have h2 (q : Pattern) (ha : d131350 q = 1) (hb : d181126 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d131350, d181126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131350, d181126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d131351 q = 1) (hb : d181127 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d131351, d181127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131351, d181127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d131368 q = 1) (hb : d181133 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d131368, d181133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131368, d181133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d131379 q = 1) (hb : d181142 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d131379, d181142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131379, d181142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d131380 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d131381 q = 1) (hb : d181143 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d131381, d181143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131381, d181143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  exact h7 p ha hb
theorem andIntro40978 (p : Pattern) (ha : d131387 p = 1) (hb : d181149 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131373 q = 1) (hb : d181136 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d131373, d181136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40975 q ha hb
    | true =>
      simp only [d131373, d181136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d131374 q = 1) (hb : d181137 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d131374, d181137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131374, d181137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d131382 q = 1) (hb : d181144 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d131382, d181144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40977 q ha hb
    | true =>
      simp only [d131382, d181144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d131383 q = 1) (hb : d181145 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d131383, d181145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131383, d181145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d131384 q = 1) (hb : d181146 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d131384, d181146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d131384, d181146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d131385 q = 1) (hb : d181147 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d131385, d181147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131385, d181147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d131386 q = 1) (hb : d181148 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d131386, d181148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d131386, d181148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d131387 q = 1) (hb : d181149 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d131387, d181149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d131387, d181149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro40979 (p : Pattern) (ha : d131398 p = 1) (hb : d181155 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131373 q = 1) (hb : d181136 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d131373, d181136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40975 q ha hb
    | true =>
      simp only [d131373, d181136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d131374 q = 1) (hb : d181137 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d131374, d181137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131374, d181137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d131395 q = 1) (hb : d181152 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d131395, d181152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d131395, d181152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d131396 q = 1) (hb : d181153 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d131396, d181153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131396, d181153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d131397 q = 1) (hb : d181154 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d131397, d181154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131397, d181154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d131398 q = 1) (hb : d181155 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d131398, d181155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131398, d181155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro40980 (p : Pattern) (ha : d131404 p = 1) (hb : d181161 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131388 q = 1) (hb : d181150 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d131388, d181150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40976 q ha hb
    | true =>
      simp only [d131388, d181150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40978 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d131393 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d131394 q = 1) (hb : d181151 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d131394, d181151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d131394, d181151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d131399 q = 1) (hb : d181156 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d131399, d181156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40979 q ha hb
    | true =>
      simp only [d131399, d181156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d131400 q = 1) (hb : d181157 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d131400, d181157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131400, d181157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d131401 q = 1) (hb : d181158 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d131401, d181158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131401, d181158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d131402 q = 1) (hb : d181159 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d131402, d181159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131402, d181159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d131403 q = 1) (hb : d181160 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d131403, d181160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131403, d181160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d131404 q = 1) (hb : d181161 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d131404, d181161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131404, d181161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro40981 (p : Pattern) (ha : d131392 p = 1) (hb : d181166 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131382 q = 1) (hb : d181144 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d131382, d181144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40977 q ha hb
    | true =>
      simp only [d131382, d181144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d131383 q = 1) (hb : d181145 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d131383, d181145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131383, d181145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d131389 q = 1) (hb : d181163 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d131389, d181163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d131389, d181163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d131390 q = 1) (hb : d181164 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d131390, d181164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131390, d181164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d131391 q = 1) (hb : d181165 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d131391, d181165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131391, d181165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d131392 q = 1) (hb : d181166 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d131392, d181166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131392, d181166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro40982 (p : Pattern) (ha : d131411 p = 1) (hb : d181172 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131406 q = 1) (hb : d181167 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d131406, d181167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40981 q ha hb
    | true =>
      simp only [d131406, d181167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d131407 q = 1) (hb : d181168 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d131407, d181168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131407, d181168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d131408 q = 1) (hb : d181169 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d131408, d181169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d131408, d181169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d131409 q = 1) (hb : d181170 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d131409, d181170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131409, d181170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d131410 q = 1) (hb : d181171 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d131410, d181171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131410, d181171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d131411 q = 1) (hb : d181172 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d131411, d181172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131411, d181172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro40983 (p : Pattern) (ha : d131417 p = 1) (hb : d181178 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131405 q = 1) (hb : d181162 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d131405, d181162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131405, d181162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40980 q ha hb
  have h2 (q : Pattern) (ha : d131412 q = 1) (hb : d181173 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d131412, d181173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131412, d181173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40982 q ha hb
  have h3 (q : Pattern) (ha : d131413 q = 1) (hb : d181174 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d131413, d181174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d131413, d181174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d131414 q = 1) (hb : d181175 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d131414, d181175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131414, d181175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d131415 q = 1) (hb : d181176 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d131415, d181176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131415, d181176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d131416 q = 1) (hb : d181177 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d131416, d181177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131416, d181177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d131417 q = 1) (hb : d181178 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d131417, d181178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131417, d181178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro40984 (p : Pattern) (ha : d131423 p = 1) (hb : d181184 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131418 q = 1) (hb : d181179 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d131418, d181179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131418, d181179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40983 q ha hb
  have h2 (q : Pattern) (ha : d131419 q = 1) (hb : d181180 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d131419, d181180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131419, d181180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d131420 q = 1) (hb : d181181 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d131420, d181181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131420, d181181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d131421 q = 1) (hb : d181182 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d131421, d181182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131421, d181182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d131422 q = 1) (hb : d181183 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d131422, d181183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131422, d181183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d131423 q = 1) (hb : d181184 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d131423, d181184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131423, d181184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro40985 (p : Pattern) (ha : d131440 p = 1) (hb : d181197 p = 1) : d0 p = 1 := by
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
  have h2 (q : Pattern) (ha : d18991 q = 1) (hb : d131426 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d18991, d131426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d18991, d131426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52792 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d131427 q = 1) (hb : d181187 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d131427, d181187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d131427, d181187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d131428 q = 1) (hb : d181188 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d131428, d181188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131428, d181188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d16649 q = 1) (hb : d127450 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d16649, d127450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16649, d127450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23310 q ha hb
  have h7 (q : Pattern) (ha : d18994 q = 1) (hb : d131429 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d18994, d131429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d18994, d131429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d101276 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d131430 q = 1) (hb : d181189 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d131430, d181189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d131430, d181189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d131431 q = 1) (hb : d181190 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d131431, d181190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d131431, d181190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d131432 q = 1) (hb : d181191 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d131432, d181191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131432, d181191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d14987 q = 1) (hb : d123112 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d14987, d123112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14987, d123112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23311 q ha hb
  have h13 (q : Pattern) (ha : d18998 q = 1) (hb : d131433 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d18998, d131433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d18998, d131433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d101286 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d131434 q = 1) (hb : d181192 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d131434, d181192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d131434, d181192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d131435 q = 1) (hb : d181193 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d131435, d181193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d131435, d181193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h17 (q : Pattern) (ha : d14994 q = 1) (hb : d123119 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d14994, d123119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14994, d123119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23313 q ha hb
  have h18 (q : Pattern) (ha : d19001 q = 1) (hb : d131436 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d19001, d131436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d19001, d131436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d0 q = 1) (hb : d101301 q = 1) : d0 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d131437 q = 1) (hb : d181194 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d131437, d181194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
    | true =>
      simp only [d131437, d181194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
  have h21 (q : Pattern) (ha : d131438 q = 1) (hb : d181195 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d131438, d181195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d131438, d181195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d131439 q = 1) (hb : d181196 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d131439, d181196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d131439, d181196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d131440 q = 1) (hb : d181197 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d131440, d181197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d131440, d181197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro40986 (p : Pattern) (ha : d131452 p = 1) (hb : d181206 p = 1) : d0 p = 1 := by
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
  have h2 (q : Pattern) (ha : d19006 q = 1) (hb : d131441 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d19006, d131441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d19006, d131441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52682 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d131442 q = 1) (hb : d181198 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d131442, d181198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d131442, d181198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d131443 q = 1) (hb : d181199 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d131443, d181199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131443, d181199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d16656 q = 1) (hb : d127457 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d16656, d127457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16656, d127457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23315 q ha hb
  have h7 (q : Pattern) (ha : d19009 q = 1) (hb : d131444 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d19009, d131444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d19009, d131444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d101312 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d131445 q = 1) (hb : d181200 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d131445, d181200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d131445, d181200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d131446 q = 1) (hb : d181201 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d131446, d181201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d131446, d181201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d131447 q = 1) (hb : d181202 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d131447, d181202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131447, d181202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d14994 q = 1) (hb : d123119 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d14994, d123119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14994, d123119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23313 q ha hb
  have h13 (q : Pattern) (ha : d19001 q = 1) (hb : d131436 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d19001, d131436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d19001, d131436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d101301 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d131437 q = 1) (hb : d181194 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d131437, d181194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d131437, d181194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d131438 q = 1) (hb : d181195 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d131438, d181195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d131438, d181195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h17 (q : Pattern) (ha : d15004 q = 1) (hb : d123129 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15004, d123129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15004, d123129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23303 q ha hb
  have h18 (q : Pattern) (ha : d19013 q = 1) (hb : d131448 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d19013, d131448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d19013, d131448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d0 q = 1) (hb : d101323 q = 1) : d0 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d131449 q = 1) (hb : d181203 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d131449, d181203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
    | true =>
      simp only [d131449, d181203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
  have h21 (q : Pattern) (ha : d131450 q = 1) (hb : d181204 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d131450, d181204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d131450, d181204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d131451 q = 1) (hb : d181205 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d131451, d181205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d131451, d181205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d131452 q = 1) (hb : d181206 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d131452, d181206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d131452, d181206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro40987 (p : Pattern) (ha : d131461 p = 1) (hb : d181214 p = 1) : d0 p = 1 := by
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
  have h2 (q : Pattern) (ha : d19021 q = 1) (hb : d131456 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d19021, d131456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d19021, d131456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d101337 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d131457 q = 1) (hb : d181210 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d131457, d181210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d131457, d181210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d131458 q = 1) (hb : d181211 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d131458, d181211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131458, d181211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d15004 q = 1) (hb : d123129 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15004, d123129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15004, d123129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23303 q ha hb
  have h7 (q : Pattern) (ha : d19013 q = 1) (hb : d131448 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d19013, d131448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d19013, d131448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d101323 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d131449 q = 1) (hb : d181203 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d131449, d181203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d131449, d181203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d131450 q = 1) (hb : d181204 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d131450, d181204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d131450, d181204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d131459 q = 1) (hb : d181212 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d131459, d181212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131459, d181212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d131460 q = 1) (hb : d181213 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d131460, d181213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d131460, d181213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d131461 q = 1) (hb : d181214 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d131461, d181214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d131461, d181214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro40988 (p : Pattern) (ha : d131473 p = 1) (hb : d181224 p = 1) : d0 p = 1 := by
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
  have h2 (q : Pattern) (ha : d19031 q = 1) (hb : d131466 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d19031, d131466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d19031, d131466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52692 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d131467 q = 1) (hb : d181219 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d131467, d181219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d131467, d181219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d131468 q = 1) (hb : d181220 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d131468, d181220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131468, d181220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d1391 q = 1) (hb : d52879 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1391, d52879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1391, d52879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro151 q ha hb
  have h7 (q : Pattern) (ha : d19034 q = 1) (hb : d131469 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d19034, d131469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d19034, d131469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52703 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d131470 q = 1) (hb : d181221 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d131470, d181221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d131470, d181221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d131471 q = 1) (hb : d181222 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d131471, d181222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d131471, d181222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d131472 q = 1) (hb : d181223 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d131472, d181223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131472, d181223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d15004 q = 1) (hb : d123129 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15004, d123129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15004, d123129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23303 q ha hb
  have h13 (q : Pattern) (ha : d19013 q = 1) (hb : d131448 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d19013, d131448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d19013, d131448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d101323 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d131449 q = 1) (hb : d181203 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d131449, d181203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d131449, d181203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d131450 q = 1) (hb : d181204 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d131450, d181204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d131450, d181204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h17 (q : Pattern) (ha : d131460 q = 1) (hb : d181213 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d131460, d181213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d131460, d181213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d131473 q = 1) (hb : d181224 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d131473, d181224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d131473, d181224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro40989 (p : Pattern) (ha : d131485 p = 1) (hb : d181234 p = 1) : d0 p = 1 := by
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
  have h2 (q : Pattern) (ha : d19042 q = 1) (hb : d131477 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d19042, d131477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d19042, d131477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d69109 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d131478 q = 1) (hb : d181228 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d131478, d181228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d131478, d181228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d131479 q = 1) (hb : d181229 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d131479, d181229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131479, d181229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d131480 q = 1) (hb : d181230 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d131480, d181230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131480, d181230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d15019 q = 1) (hb : d123144 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15019, d123144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15019, d123144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23305 q ha hb
  have h8 (q : Pattern) (ha : d19046 q = 1) (hb : d131481 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d19046, d131481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d19046, d131481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d101367 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d131482 q = 1) (hb : d181231 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d131482, d181231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d131482, d181231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d131483 q = 1) (hb : d181232 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d131483, d181232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d131483, d181232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d131484 q = 1) (hb : d181233 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d131484, d181233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d131484, d181233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d131485 q = 1) (hb : d181234 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d131485, d181234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d131485, d181234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro40990 (p : Pattern) (ha : d131502 p = 1) (hb : d181240 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131453 q = 1) (hb : d181207 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d131453, d181207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40985 q ha hb
    | true =>
      simp only [d131453, d181207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40986 q ha hb
  have h2 (q : Pattern) (ha : d131454 q = 1) (hb : d181208 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d131454, d181208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131454, d181208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d131455 q = 1) (hb : d181209 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d131455, d181209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131455, d181209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d131462 q = 1) (hb : d181215 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d131462, d181215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40986 q ha hb
    | true =>
      simp only [d131462, d181215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40987 q ha hb
  have h5 (q : Pattern) (ha : d131463 q = 1) (hb : d181216 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d131463, d181216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131463, d181216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d131464 q = 1) (hb : d181217 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d131464, d181217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131464, d181217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d131465 q = 1) (hb : d181218 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d131465, d181218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131465, d181218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d131474 q = 1) (hb : d181225 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d131474, d181225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40986 q ha hb
    | true =>
      simp only [d131474, d181225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40988 q ha hb
  have h9 (q : Pattern) (ha : d131475 q = 1) (hb : d181226 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d131475, d181226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131475, d181226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d131476 q = 1) (hb : d181227 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d131476, d181227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131476, d181227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d131486 q = 1) (hb : d181235 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d131486, d181235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40988 q ha hb
    | true =>
      simp only [d131486, d181235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40989 q ha hb
  have h12 (q : Pattern) (ha : d131487 q = 1) (hb : d181236 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d131487, d181236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131487, d181236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d131488 q = 1) (hb : d181237 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d131488, d181237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131488, d181237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d131489 q = 1) (hb : d181238 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d131489, d181238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d131489, d181238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d131490 q = 1) (hb : d181239 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d131490, d181239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d131490, d181239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d0 q = 1) (hb : d131501 q = 1) : d0 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d131502 q = 1) (hb : d181240 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d131502, d181240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d131502, d181240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q hb ha
  exact h17 p ha hb
theorem andIntro40991 (p : Pattern) (ha : d131509 p = 1) (hb : d181245 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131474 q = 1) (hb : d181225 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d131474, d181225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40986 q ha hb
    | true =>
      simp only [d131474, d181225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40988 q ha hb
  have h2 (q : Pattern) (ha : d131475 q = 1) (hb : d181226 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d131475, d181226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131475, d181226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d131476 q = 1) (hb : d181227 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d131476, d181227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131476, d181227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d131486 q = 1) (hb : d181235 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d131486, d181235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40988 q ha hb
    | true =>
      simp only [d131486, d181235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40989 q ha hb
  have h5 (q : Pattern) (ha : d131487 q = 1) (hb : d181236 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d131487, d181236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131487, d181236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d131488 q = 1) (hb : d181237 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d131488, d181237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131488, d181237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d131489 q = 1) (hb : d181238 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d131489, d181238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131489, d181238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d131505 q = 1) (hb : d181243 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d131505, d181243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d131505, d181243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d131506 q = 1) (hb : d181244 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d131506, d181244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d131506, d181244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d131508 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d131509 q = 1) (hb : d181245 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d131509, d181245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d131509, d181245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro40992 (p : Pattern) (ha : d131515 p = 1) (hb : d181251 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131503 q = 1) (hb : d181241 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d131503, d181241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40990 q ha hb
    | true =>
      simp only [d131503, d181241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d131504 q = 1) (hb : d181242 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d131504, d181242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131504, d181242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d131510 q = 1) (hb : d181246 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d131510, d181246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40991 q ha hb
    | true =>
      simp only [d131510, d181246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d131511 q = 1) (hb : d181247 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d131511, d181247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131511, d181247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d131512 q = 1) (hb : d181248 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d131512, d181248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d131512, d181248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d131513 q = 1) (hb : d181249 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d131513, d181249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131513, d181249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d131514 q = 1) (hb : d181250 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d131514, d181250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d131514, d181250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d131515 q = 1) (hb : d181251 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d131515, d181251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d131515, d181251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro40993 (p : Pattern) (ha : d131517 p = 1) (hb : d181253 p = 1) : d0 p = 1 := by
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
  have h2 (q : Pattern) (ha : d19034 q = 1) (hb : d131469 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d19034, d131469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d19034, d131469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52703 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d131470 q = 1) (hb : d181221 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d131470, d181221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d131470, d181221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d131471 q = 1) (hb : d181222 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d131471, d181222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131471, d181222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d131516 q = 1) (hb : d181252 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d131516, d181252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131516, d181252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d15019 q = 1) (hb : d123144 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15019, d123144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15019, d123144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23305 q ha hb
  have h8 (q : Pattern) (ha : d19046 q = 1) (hb : d131481 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d19046, d131481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d19046, d131481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d101367 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d131482 q = 1) (hb : d181231 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d131482, d181231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d131482, d181231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d131483 q = 1) (hb : d181232 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d131483, d181232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d131483, d181232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d131484 q = 1) (hb : d181233 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d131484, d181233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d131484, d181233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d131517 q = 1) (hb : d181253 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d131517, d181253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d131517, d181253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro40994 (p : Pattern) (ha : d131527 p = 1) (hb : d181259 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131518 q = 1) (hb : d181254 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d131518, d181254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40988 q ha hb
    | true =>
      simp only [d131518, d181254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40993 q ha hb
  have h2 (q : Pattern) (ha : d131519 q = 1) (hb : d181255 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d131519, d181255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131519, d181255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d131520 q = 1) (hb : d181256 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d131520, d181256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131520, d181256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d131521 q = 1) (hb : d181257 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d131521, d181257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131521, d181257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d131522 q = 1) (hb : d181258 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d131522, d181258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131522, d181258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d131526 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d131527 q = 1) (hb : d181259 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d131527, d181259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131527, d181259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  exact h7 p ha hb
theorem andIntro40995 (p : Pattern) (ha : d131533 p = 1) (hb : d181265 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131510 q = 1) (hb : d181246 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d131510, d181246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40991 q ha hb
    | true =>
      simp only [d131510, d181246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d131511 q = 1) (hb : d181247 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d131511, d181247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131511, d181247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d131528 q = 1) (hb : d181260 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d131528, d181260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40994 q ha hb
    | true =>
      simp only [d131528, d181260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d131529 q = 1) (hb : d181261 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d131529, d181261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131529, d181261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d131530 q = 1) (hb : d181262 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d131530, d181262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d131530, d181262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d131531 q = 1) (hb : d181263 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d131531, d181263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131531, d181263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d131532 q = 1) (hb : d181264 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d131532, d181264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d131532, d181264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d131533 q = 1) (hb : d181265 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d131533, d181265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d131533, d181265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro40996 (p : Pattern) (ha : d131550 p = 1) (hb : d181268 p = 1) : d0 p = 1 := by
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
  have h2 (q : Pattern) (ha : d19034 q = 1) (hb : d131469 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d19034, d131469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d19034, d131469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52703 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d131470 q = 1) (hb : d181221 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d131470, d181221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d131470, d181221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d131471 q = 1) (hb : d181222 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d131471, d181222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131471, d181222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d131516 q = 1) (hb : d181252 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d131516, d181252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131516, d181252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d131550 q = 1) (hb : d181268 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d131550, d181268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d131550, d181268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro40997 (p : Pattern) (ha : d131560 p = 1) (hb : d181274 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131474 q = 1) (hb : d181225 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d131474, d181225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40986 q ha hb
    | true =>
      simp only [d131474, d181225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40988 q ha hb
  have h2 (q : Pattern) (ha : d131475 q = 1) (hb : d181226 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d131475, d181226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131475, d181226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d131476 q = 1) (hb : d181227 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d131476, d181227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131476, d181227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d131486 q = 1) (hb : d181235 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d131486, d181235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40988 q ha hb
    | true =>
      simp only [d131486, d181235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40989 q ha hb
  have h5 (q : Pattern) (ha : d131487 q = 1) (hb : d181236 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d131487, d181236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131487, d181236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d131488 q = 1) (hb : d181237 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d131488, d181237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131488, d181237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d131489 q = 1) (hb : d181238 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d131489, d181238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131489, d181238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d131551 q = 1) (hb : d181269 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d131551, d181269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40988 q ha hb
    | true =>
      simp only [d131551, d181269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40996 q ha hb
  have h9 (q : Pattern) (ha : d131552 q = 1) (hb : d181270 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d131552, d181270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131552, d181270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d131553 q = 1) (hb : d181271 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d131553, d181271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131553, d181271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d131554 q = 1) (hb : d181272 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d131554, d181272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d131554, d181272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d131555 q = 1) (hb : d181273 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d131555, d181273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d131555, d181273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d131559 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d131560 q = 1) (hb : d181274 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d131560, d181274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d131560, d181274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  exact h14 p ha hb
theorem andIntro40998 (p : Pattern) (ha : d131566 p = 1) (hb : d181280 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131561 q = 1) (hb : d181275 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d131561, d181275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40997 q ha hb
    | true =>
      simp only [d131561, d181275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d131562 q = 1) (hb : d181276 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d131562, d181276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131562, d181276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d131563 q = 1) (hb : d181277 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d131563, d181277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d131563, d181277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d131564 q = 1) (hb : d181278 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d131564, d181278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131564, d181278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d131565 q = 1) (hb : d181279 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d131565, d181279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131565, d181279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d131566 q = 1) (hb : d181280 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d131566, d181280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131566, d181280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro40999 (p : Pattern) (ha : d131572 p = 1) (hb : d181286 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131534 q = 1) (hb : d181266 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d131534, d181266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40992 q ha hb
    | true =>
      simp only [d131534, d181266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40995 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d131548 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d131549 q = 1) (hb : d181267 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d131549, d181267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d131549, d181267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d131567 q = 1) (hb : d181281 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d131567, d181281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40998 q ha hb
    | true =>
      simp only [d131567, d181281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d131568 q = 1) (hb : d181282 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d131568, d181282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131568, d181282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d131569 q = 1) (hb : d181283 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d131569, d181283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131569, d181283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d131570 q = 1) (hb : d181284 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d131570, d181284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131570, d181284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d131571 q = 1) (hb : d181285 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d131571, d181285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131571, d181285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d131572 q = 1) (hb : d181286 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d131572, d181286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131572, d181286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
end NetHack.Soko22Hazard87
