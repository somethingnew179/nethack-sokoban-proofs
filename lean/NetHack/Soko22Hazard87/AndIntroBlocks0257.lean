import NetHack.Soko22Hazard87.AndIntroBlocks0256
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro64250 (p : Pattern) (ha : d256860 p = 1) (hb : d258360 p = 1) : d259550 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d256850 q = 1) (hb : d258338 q = 1) : d259528 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d256850, d258338, d259528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64246 q ha hb
    | true =>
      simp only [d256850, d258338, d259528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d256851 q = 1) (hb : d258339 q = 1) : d259529 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d256851, d258339, d259529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d256851, d258339, d259529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d256857 q = 1) (hb : d258357 q = 1) : d259547 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d256857, d258357, d259547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d256857, d258357, d259547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d256858 q = 1) (hb : d258358 q = 1) : d259548 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d256858, d258358, d259548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d256858, d258358, d259548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d256859 q = 1) (hb : d258359 q = 1) : d259549 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d256859, d258359, d259549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d256859, d258359, d259549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d256860 q = 1) (hb : d258360 q = 1) : d259550 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d256860, d258360, d259550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d256860, d258360, d259550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro64251 (p : Pattern) (ha : d256879 p = 1) (hb : d258366 p = 1) : d259556 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d256874 q = 1) (hb : d258361 q = 1) : d259551 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d256874, d258361, d259551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64250 q ha hb
    | true =>
      simp only [d256874, d258361, d259551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d256875 q = 1) (hb : d258362 q = 1) : d259552 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d256875, d258362, d259552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d256875, d258362, d259552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d256876 q = 1) (hb : d258363 q = 1) : d259553 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d256876, d258363, d259553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d256876, d258363, d259553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d256877 q = 1) (hb : d258364 q = 1) : d259554 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d256877, d258364, d259554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d256877, d258364, d259554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d256878 q = 1) (hb : d258365 q = 1) : d259555 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d256878, d258365, d259555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d256878, d258365, d259555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d256879 q = 1) (hb : d258366 q = 1) : d259556 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d256879, d258366, d259556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d256879, d258366, d259556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro64252 (p : Pattern) (ha : d256885 p = 1) (hb : d258372 p = 1) : d259562 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d256650 q = 1) (hb : d258153 q = 1) : d259354 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d256650, d258153, d259354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d256650, d258153, d259354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64210 q ha hb
  have h2 (q : Pattern) (ha : d256651 q = 1) (hb : d258154 q = 1) : d259355 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d256651, d258154, d259355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d256651, d258154, d259355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d256660 q = 1) (hb : d258163 q = 1) : d259364 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d256660, d258163, d259364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64210 q ha hb
    | true =>
      simp only [d256660, d258163, d259364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64213 q ha hb
  have h4 (q : Pattern) (ha : d256661 q = 1) (hb : d258164 q = 1) : d259365 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d256661, d258164, d259365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d256661, d258164, d259365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d256662 q = 1) (hb : d258165 q = 1) : d259366 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d256662, d258165, d259366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d256662, d258165, d259366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d256750 q = 1) (hb : d258247 q = 1) : d259441 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d256750, d258247, d259441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64226 q ha hb
    | true =>
      simp only [d256750, d258247, d259441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64233 q ha hb
  have h7 (q : Pattern) (ha : d256763 q = 1) (hb : d258260 q = 1) : d259454 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d256763, d258260, d259454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64234 q ha hb
    | true =>
      simp only [d256763, d258260, d259454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64235 q ha hb
  have h8 (q : Pattern) (ha : d256764 q = 1) (hb : d258261 q = 1) : d259455 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d256764, d258261, d259455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d256764, d258261, d259455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d256765 q = 1) (hb : d258262 q = 1) : d259456 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d256765, d258262, d259456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d256765, d258262, d259456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d256766 q = 1) (hb : d258263 q = 1) : d259457 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d256766, d258263, d259457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d256766, d258263, d259457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d256770 q = 1) (hb : d258267 q = 1) : d259461 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d256770, d258267, d259461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d256770, d258267, d259461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64236 q ha hb
  have h12 (q : Pattern) (ha : d256772 q = 1) (hb : d258269 q = 1) : d259463 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d256772, d258269, d259463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d256772, d258269, d259463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64237 q ha hb
  have h13 (q : Pattern) (ha : d256773 q = 1) (hb : d258270 q = 1) : d259464 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d256773, d258270, d259464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d256773, d258270, d259464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d256774 q = 1) (hb : d258271 q = 1) : d259465 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d256774, d258271, d259465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d256774, d258271, d259465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d256775 q = 1) (hb : d258272 q = 1) : d259466 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d256775, d258272, d259466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d256775, d258272, d259466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d256776 q = 1) (hb : d258273 q = 1) : d259467 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d256776, d258273, d259467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d256776, d258273, d259467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d256873 q = 1) (hb : d258356 q = 1) : d259546 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d256873, d258356, d259546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d256873, d258356, d259546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64249 q ha hb
  have h18 (q : Pattern) (ha : d256880 q = 1) (hb : d258367 q = 1) : d259557 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d256880, d258367, d259557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d256880, d258367, d259557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64251 q ha hb
  have h19 (q : Pattern) (ha : d256881 q = 1) (hb : d258368 q = 1) : d259558 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d256881, d258368, d259558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d256881, d258368, d259558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d256882 q = 1) (hb : d258369 q = 1) : d259559 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d256882, d258369, d259559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d256882, d258369, d259559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d256883 q = 1) (hb : d258370 q = 1) : d259560 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d256883, d258370, d259560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d256883, d258370, d259560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d256884 q = 1) (hb : d258371 q = 1) : d259561 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d256884, d258371, d259561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d256884, d258371, d259561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d256885 q = 1) (hb : d258372 q = 1) : d259562 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d256885, d258372, d259562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d256885, d258372, d259562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro64253 (p : Pattern) (ha : d256891 p = 1) (hb : d258378 p = 1) : d259568 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d256886 q = 1) (hb : d258373 q = 1) : d259563 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d256886, d258373, d259563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d256886, d258373, d259563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64252 q ha hb
  have h2 (q : Pattern) (ha : d256887 q = 1) (hb : d258374 q = 1) : d259564 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d256887, d258374, d259564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d256887, d258374, d259564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d256888 q = 1) (hb : d258375 q = 1) : d259565 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d256888, d258375, d259565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d256888, d258375, d259565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d256889 q = 1) (hb : d258376 q = 1) : d259566 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d256889, d258376, d259566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d256889, d258376, d259566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d256890 q = 1) (hb : d258377 q = 1) : d259567 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d256890, d258377, d259567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d256890, d258377, d259567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d256891 q = 1) (hb : d258378 q = 1) : d259568 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d256891, d258378, d259568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d256891, d258378, d259568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro64254 (p : Pattern) (ha : d256045 p = 1) (hb : d258385 p = 1) : d258695 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d256045 q = 1) : d0 q = 1 := by
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
  have h3 (q : Pattern) (ha : d1 q = 1) (hb : d13 q = 1) : d13 q = 1 := by
    exact hb
  have h4 (q : Pattern) (ha : d128 q = 1) (hb : d52107 q = 1) : d44880 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d128, d52107, d44880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d128, d52107, d44880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d52107 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d2016 q = 1) (hb : d52107 q = 1) : d46864 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d2016, d46864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2016, d46864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d2021 q = 1) (hb : d256041 q = 1) : d46865 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d2021, d256041, d46865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d2021, d256041, d46865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d2022 q = 1) (hb : d256045 q = 1) : d46866 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d2022, d256045, d46866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2022, d256045, d46866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h9 (q : Pattern) (ha : d256045 q = 1) (hb : d258385 q = 1) : d258695 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d258385, d258695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d258385, d258695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  exact h9 p ha hb
theorem andIntro64255 (p : Pattern) (ha : d256896 p = 1) (hb : d258383 p = 1) : d259574 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d256896 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d1997 q = 1) : d1997 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d13 q = 1) (hb : d127 q = 1) : d0 q = 1 := by
    cases bit : q 248 with
    | false =>
      simp only [d13, d127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d13, d127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1 q = 1) (hb : d13 q = 1) : d13 q = 1 := by
    exact hb
  have h5 (q : Pattern) (ha : d128 q = 1) (hb : d52107 q = 1) : d44880 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d128, d52107, d44880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d128, d52107, d44880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d52107 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d2016 q = 1) (hb : d52107 q = 1) : d46864 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d2016, d46864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2016, d46864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d2017 q = 1) (hb : d255849 q = 1) : d258806 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d2017, d255849, d258806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d2017, d255849, d258806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d2018 q = 1) (hb : d256896 q = 1) : d259573 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d2018, d256896, d259573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d2018, d256896, d259573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h10 (q : Pattern) (ha : d256896 q = 1) (hb : d258383 q = 1) : d259574 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d258383, d259574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d258383, d259574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  exact h10 p ha hb
theorem andIntro64256 (p : Pattern) (ha : d256903 p = 1) (hb : d258391 p = 1) : d259581 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d258184 q = 1) : d258184 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d257871 q = 1) : d257871 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d256897 q = 1) (hb : d258384 q = 1) : d259575 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d256897, d258384, d259575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d256897, d258384, d259575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64255 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d256898 q = 1) (hb : d258386 q = 1) : d259576 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d256898, d258386, d259576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d256898, d258386, d259576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64254 q ha hb
  have h5 (q : Pattern) (ha : d256899 q = 1) (hb : d258387 q = 1) : d259577 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d256899, d258387, d259577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d256899, d258387, d259577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d256900 q = 1) (hb : d258388 q = 1) : d259578 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d256900, d258388, d259578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d256900, d258388, d259578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h7 (q : Pattern) (ha : d256901 q = 1) (hb : d258389 q = 1) : d259579 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d256901, d258389, d259579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d256901, d258389, d259579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h8 (q : Pattern) (ha : d256902 q = 1) (hb : d258390 q = 1) : d259580 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d256902, d258390, d259580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d256902, d258390, d259580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h9 (q : Pattern) (ha : d256903 q = 1) (hb : d258391 q = 1) : d259581 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d256903, d258391, d259581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d256903, d258391, d259581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro64257 (p : Pattern) (ha : d256909 p = 1) (hb : d258397 p = 1) : d259587 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d257871 q = 1) : d257871 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d256897 q = 1) (hb : d258384 q = 1) : d259575 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d256897, d258384, d259575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d256897, d258384, d259575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64255 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d256898 q = 1) (hb : d258386 q = 1) : d259576 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d256898, d258386, d259576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d256898, d258386, d259576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64254 q ha hb
  have h4 (q : Pattern) (ha : d256899 q = 1) (hb : d258387 q = 1) : d259577 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d256899, d258387, d259577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d256899, d258387, d259577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d256900 q = 1) (hb : d258388 q = 1) : d259578 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d256900, d258388, d259578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d256900, d258388, d259578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h6 (q : Pattern) (ha : d256901 q = 1) (hb : d258389 q = 1) : d259579 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d256901, d258389, d259579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d256901, d258389, d259579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h7 (q : Pattern) (ha : d256902 q = 1) (hb : d258390 q = 1) : d259580 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d256902, d258390, d259580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d256902, d258390, d259580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h8 (q : Pattern) (ha : d256909 q = 1) (hb : d258397 q = 1) : d259587 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d256909, d258397, d259587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d256909, d258397, d259587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  exact h8 p ha hb
theorem andIntro64258 (p : Pattern) (ha : d256915 p = 1) (hb : d258403 p = 1) : d259593 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d258189 q = 1) : d258189 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d256904 q = 1) (hb : d258392 q = 1) : d259582 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d256904, d258392, d259582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64256 q ha hb
    | true =>
      simp only [d256904, d258392, d259582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d256905 q = 1) (hb : d258393 q = 1) : d259583 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d256905, d258393, d259583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d256905, d258393, d259583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h4 (q : Pattern) (ha : d256906 q = 1) (hb : d258394 q = 1) : d259584 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d256906, d258394, d259584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d256906, d258394, d259584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d256907 q = 1) (hb : d258395 q = 1) : d259585 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d256907, d258395, d259585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d256907, d258395, d259585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h6 (q : Pattern) (ha : d256908 q = 1) (hb : d258396 q = 1) : d259586 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d256908, d258396, d259586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d256908, d258396, d259586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d256910 q = 1) (hb : d258398 q = 1) : d259588 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d256910, d258398, d259588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64257 q ha hb
    | true =>
      simp only [d256910, d258398, d259588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h8 (q : Pattern) (ha : d256911 q = 1) (hb : d258399 q = 1) : d259589 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d256911, d258399, d259589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d256911, d258399, d259589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h9 (q : Pattern) (ha : d256912 q = 1) (hb : d258400 q = 1) : d259590 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d256912, d258400, d259590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d256912, d258400, d259590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d256913 q = 1) (hb : d258401 q = 1) : d259591 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d256913, d258401, d259591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d256913, d258401, d259591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h11 (q : Pattern) (ha : d256914 q = 1) (hb : d258402 q = 1) : d259592 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d256914, d258402, d259592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d256914, d258402, d259592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d256915 q = 1) (hb : d258403 q = 1) : d259593 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d256915, d258403, d259593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d256915, d258403, d259593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro64259 (p : Pattern) (ha : d256909 p = 1) (hb : d258406 p = 1) : d259596 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d257871 q = 1) : d257871 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d256897 q = 1) (hb : d258384 q = 1) : d259575 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d256897, d258384, d259575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d256897, d258384, d259575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64255 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d256898 q = 1) (hb : d258386 q = 1) : d259576 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d256898, d258386, d259576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d256898, d258386, d259576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64254 q ha hb
  have h4 (q : Pattern) (ha : d256899 q = 1) (hb : d258387 q = 1) : d259577 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d256899, d258387, d259577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d256899, d258387, d259577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d256900 q = 1) (hb : d258388 q = 1) : d259578 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d256900, d258388, d259578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d256900, d258388, d259578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h6 (q : Pattern) (ha : d1 q = 1) (hb : d27032 q = 1) : d27032 q = 1 := by
    exact hb
  have h7 (q : Pattern) (ha : d256901 q = 1) (hb : d258404 q = 1) : d259594 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d256901, d258404, d259594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d256901, d258404, d259594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d256902 q = 1) (hb : d258405 q = 1) : d259595 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d256902, d258405, d259595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d256902, d258405, d259595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h9 (q : Pattern) (ha : d256909 q = 1) (hb : d258406 q = 1) : d259596 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d256909, d258406, d259596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d256909, d258406, d259596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  exact h9 p ha hb
theorem andIntro64260 (p : Pattern) (ha : d256917 p = 1) (hb : d258413 p = 1) : d259603 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d256904 q = 1) (hb : d258392 q = 1) : d259582 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d256904, d258392, d259582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64256 q ha hb
    | true =>
      simp only [d256904, d258392, d259582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d256905 q = 1) (hb : d258393 q = 1) : d259583 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d256905, d258393, d259583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d256905, d258393, d259583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d256906 q = 1) (hb : d258394 q = 1) : d259584 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d256906, d258394, d259584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d256906, d258394, d259584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d256907 q = 1) (hb : d258395 q = 1) : d259585 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d256907, d258395, d259585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d256907, d258395, d259585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d256910 q = 1) (hb : d258407 q = 1) : d259597 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d256910, d258407, d259597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64259 q ha hb
    | true =>
      simp only [d256910, d258407, d259597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d256911 q = 1) (hb : d258408 q = 1) : d259598 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d256911, d258408, d259598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d256911, d258408, d259598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d256912 q = 1) (hb : d258409 q = 1) : d259599 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d256912, d258409, d259599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d256912, d258409, d259599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d256913 q = 1) (hb : d258410 q = 1) : d259600 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d256913, d258410, d259600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d256913, d258410, d259600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d256914 q = 1) (hb : d258411 q = 1) : d259601 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d256914, d258411, d259601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d256914, d258411, d259601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d256910 q = 1) (hb : d258398 q = 1) : d259588 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d256910, d258398, d259588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64257 q ha hb
    | true =>
      simp only [d256910, d258398, d259588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d256911 q = 1) (hb : d258399 q = 1) : d259589 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d256911, d258399, d259589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d256911, d258399, d259589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d256912 q = 1) (hb : d258400 q = 1) : d259590 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d256912, d258400, d259590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d256912, d258400, d259590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d256913 q = 1) (hb : d258401 q = 1) : d259591 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d256913, d258401, d259591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d256913, d258401, d259591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d256916 q = 1) (hb : d258412 q = 1) : d259602 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d256916, d258412, d259602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d256916, d258412, d259602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d256917 q = 1) (hb : d258413 q = 1) : d259603 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d256917, d258413, d259603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d256917, d258413, d259603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro64261 (p : Pattern) (ha : d256921 p = 1) (hb : d258418 p = 1) : d259608 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d256910 q = 1) (hb : d258407 q = 1) : d259597 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d256910, d258407, d259597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64259 q ha hb
    | true =>
      simp only [d256910, d258407, d259597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d256911 q = 1) (hb : d258408 q = 1) : d259598 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d256911, d258408, d259598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d256911, d258408, d259598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d256912 q = 1) (hb : d258409 q = 1) : d259599 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d256912, d258409, d259599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d256912, d258409, d259599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d256913 q = 1) (hb : d258410 q = 1) : d259600 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d256913, d258410, d259600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d256913, d258410, d259600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d256916 q = 1) (hb : d258417 q = 1) : d259607 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d256916, d258417, d259607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d256916, d258417, d259607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d256921 q = 1) (hb : d258418 q = 1) : d259608 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d256921, d258418, d259608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d256921, d258418, d259608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro64262 (p : Pattern) (ha : d256928 p = 1) (hb : d258425 p = 1) : d259615 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d256918 q = 1) (hb : d258414 q = 1) : d259604 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d256918, d258414, d259604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64258 q ha hb
    | true =>
      simp only [d256918, d258414, d259604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64260 q ha hb
  have h2 (q : Pattern) (ha : d256919 q = 1) (hb : d258415 q = 1) : d259605 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d256919, d258415, d259605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d256919, d258415, d259605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d256920 q = 1) (hb : d258416 q = 1) : d259606 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d256920, d258416, d259606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d256920, d258416, d259606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d256922 q = 1) (hb : d258419 q = 1) : d259609 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d256922, d258419, d259609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64260 q ha hb
    | true =>
      simp only [d256922, d258419, d259609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64261 q ha hb
  have h5 (q : Pattern) (ha : d256923 q = 1) (hb : d258420 q = 1) : d259610 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d256923, d258420, d259610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d256923, d258420, d259610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d256924 q = 1) (hb : d258421 q = 1) : d259611 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d256924, d258421, d259611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d256924, d258421, d259611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d256925 q = 1) (hb : d258422 q = 1) : d259612 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d256925, d258422, d259612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d256925, d258422, d259612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d256926 q = 1) (hb : d258423 q = 1) : d259613 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d256926, d258423, d259613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d256926, d258423, d259613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d256927 q = 1) (hb : d258424 q = 1) : d259614 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d256927, d258424, d259614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d256927, d258424, d259614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d256928 q = 1) (hb : d258425 q = 1) : d259615 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d256928, d258425, d259615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d256928, d258425, d259615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro64263 (p : Pattern) (ha : d256932 p = 1) (hb : d258429 p = 1) : d259619 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d256922 q = 1) (hb : d258419 q = 1) : d259609 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d256922, d258419, d259609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64260 q ha hb
    | true =>
      simp only [d256922, d258419, d259609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64261 q ha hb
  have h2 (q : Pattern) (ha : d256923 q = 1) (hb : d258420 q = 1) : d259610 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d256923, d258420, d259610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d256923, d258420, d259610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d256924 q = 1) (hb : d258421 q = 1) : d259611 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d256924, d258421, d259611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d256924, d258421, d259611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d256926 q = 1) (hb : d258423 q = 1) : d259613 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d256926, d258423, d259613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d256926, d258423, d259613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d256931 q = 1) (hb : d258428 q = 1) : d259618 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d256931, d258428, d259618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d256931, d258428, d259618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d256932 q = 1) (hb : d258429 q = 1) : d259619 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d256932, d258429, d259619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d256932, d258429, d259619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro64264 (p : Pattern) (ha : d256938 p = 1) (hb : d258435 p = 1) : d259625 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d256929 q = 1) (hb : d258426 q = 1) : d259616 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d256929, d258426, d259616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64262 q ha hb
    | true =>
      simp only [d256929, d258426, d259616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d256930 q = 1) (hb : d258427 q = 1) : d259617 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d256930, d258427, d259617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d256930, d258427, d259617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d256933 q = 1) (hb : d258430 q = 1) : d259620 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d256933, d258430, d259620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64263 q ha hb
    | true =>
      simp only [d256933, d258430, d259620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d256934 q = 1) (hb : d258431 q = 1) : d259621 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d256934, d258431, d259621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d256934, d258431, d259621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d256935 q = 1) (hb : d258432 q = 1) : d259622 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d256935, d258432, d259622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d256935, d258432, d259622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d256936 q = 1) (hb : d258433 q = 1) : d259623 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d256936, d258433, d259623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d256936, d258433, d259623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d256937 q = 1) (hb : d258434 q = 1) : d259624 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d256937, d258434, d259624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d256937, d258434, d259624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d256938 q = 1) (hb : d258435 q = 1) : d259625 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d256938, d258435, d259625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d256938, d258435, d259625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro64265 (p : Pattern) (ha : d256942 p = 1) (hb : d258439 p = 1) : d259629 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d256933 q = 1) (hb : d258430 q = 1) : d259620 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d256933, d258430, d259620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64263 q ha hb
    | true =>
      simp only [d256933, d258430, d259620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d256934 q = 1) (hb : d258431 q = 1) : d259621 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d256934, d258431, d259621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d256934, d258431, d259621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d256939 q = 1) (hb : d258436 q = 1) : d259626 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d256939, d258436, d259626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d256939, d258436, d259626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d256940 q = 1) (hb : d258437 q = 1) : d259627 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d256940, d258437, d259627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d256940, d258437, d259627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d256941 q = 1) (hb : d258438 q = 1) : d259628 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d256941, d258438, d259628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d256941, d258438, d259628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d256942 q = 1) (hb : d258439 q = 1) : d259629 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d256942, d258439, d259629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d256942, d258439, d259629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro64266 (p : Pattern) (ha : d256948 p = 1) (hb : d258445 p = 1) : d259635 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d256943 q = 1) (hb : d258440 q = 1) : d259630 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d256943, d258440, d259630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64264 q ha hb
    | true =>
      simp only [d256943, d258440, d259630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64265 q ha hb
  have h2 (q : Pattern) (ha : d256944 q = 1) (hb : d258441 q = 1) : d259631 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d256944, d258441, d259631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d256944, d258441, d259631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d256945 q = 1) (hb : d258442 q = 1) : d259632 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d256945, d258442, d259632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d256945, d258442, d259632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d256946 q = 1) (hb : d258443 q = 1) : d259633 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d256946, d258443, d259633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d256946, d258443, d259633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d256947 q = 1) (hb : d258444 q = 1) : d259634 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d256947, d258444, d259634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d256947, d258444, d259634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d256948 q = 1) (hb : d258445 q = 1) : d259635 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d256948, d258445, d259635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d256948, d258445, d259635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro64267 (p : Pattern) (ha : d256951 p = 1) (hb : d258448 p = 1) : d259638 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d256929 q = 1) (hb : d258426 q = 1) : d259616 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d256929, d258426, d259616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64262 q ha hb
    | true =>
      simp only [d256929, d258426, d259616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d256930 q = 1) (hb : d258427 q = 1) : d259617 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d256930, d258427, d259617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d256930, d258427, d259617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d256933 q = 1) (hb : d258430 q = 1) : d259620 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d256933, d258430, d259620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64263 q ha hb
    | true =>
      simp only [d256933, d258430, d259620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d256934 q = 1) (hb : d258431 q = 1) : d259621 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d256934, d258431, d259621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d256934, d258431, d259621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d256935 q = 1) (hb : d258432 q = 1) : d259622 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d256935, d258432, d259622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d256935, d258432, d259622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d256936 q = 1) (hb : d258433 q = 1) : d259623 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d256936, d258433, d259623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d256936, d258433, d259623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d256937 q = 1) (hb : d258434 q = 1) : d259624 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d256937, d258434, d259624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d256937, d258434, d259624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d256951 q = 1) (hb : d258448 q = 1) : d259638 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d256951, d258448, d259638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d256951, d258448, d259638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro64268 (p : Pattern) (ha : d256952 p = 1) (hb : d258449 p = 1) : d259639 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d256933 q = 1) (hb : d258430 q = 1) : d259620 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d256933, d258430, d259620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64263 q ha hb
    | true =>
      simp only [d256933, d258430, d259620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d256934 q = 1) (hb : d258431 q = 1) : d259621 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d256934, d258431, d259621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d256934, d258431, d259621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d256939 q = 1) (hb : d258436 q = 1) : d259626 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d256939, d258436, d259626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d256939, d258436, d259626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d256940 q = 1) (hb : d258437 q = 1) : d259627 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d256940, d258437, d259627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d256940, d258437, d259627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d256941 q = 1) (hb : d258438 q = 1) : d259628 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d256941, d258438, d259628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d256941, d258438, d259628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d256952 q = 1) (hb : d258449 q = 1) : d259639 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d256952, d258449, d259639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d256952, d258449, d259639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro64269 (p : Pattern) (ha : d256958 p = 1) (hb : d258455 p = 1) : d259645 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d256943 q = 1) (hb : d258440 q = 1) : d259630 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d256943, d258440, d259630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64264 q ha hb
    | true =>
      simp only [d256943, d258440, d259630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64265 q ha hb
  have h2 (q : Pattern) (ha : d256944 q = 1) (hb : d258441 q = 1) : d259631 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d256944, d258441, d259631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d256944, d258441, d259631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d256945 q = 1) (hb : d258442 q = 1) : d259632 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d256945, d258442, d259632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d256945, d258442, d259632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d256946 q = 1) (hb : d258443 q = 1) : d259633 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d256946, d258443, d259633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d256946, d258443, d259633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d256947 q = 1) (hb : d258444 q = 1) : d259634 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d256947, d258444, d259634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d256947, d258444, d259634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d256953 q = 1) (hb : d258450 q = 1) : d259640 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d256953, d258450, d259640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64267 q ha hb
    | true =>
      simp only [d256953, d258450, d259640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64268 q ha hb
  have h7 (q : Pattern) (ha : d256954 q = 1) (hb : d258451 q = 1) : d259641 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d256954, d258451, d259641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d256954, d258451, d259641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d256955 q = 1) (hb : d258452 q = 1) : d259642 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d256955, d258452, d259642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d256955, d258452, d259642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d256956 q = 1) (hb : d258453 q = 1) : d259643 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d256956, d258453, d259643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d256956, d258453, d259643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d256957 q = 1) (hb : d258454 q = 1) : d259644 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d256957, d258454, d259644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d256957, d258454, d259644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d256958 q = 1) (hb : d258455 q = 1) : d259645 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d256958, d258455, d259645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d256958, d258455, d259645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro64270 (p : Pattern) (ha : d256963 p = 1) (hb : d258460 p = 1) : d259650 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d256929 q = 1) (hb : d258426 q = 1) : d259616 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d256929, d258426, d259616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64262 q ha hb
    | true =>
      simp only [d256929, d258426, d259616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d256930 q = 1) (hb : d258427 q = 1) : d259617 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d256930, d258427, d259617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d256930, d258427, d259617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d256933 q = 1) (hb : d258430 q = 1) : d259620 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d256933, d258430, d259620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64263 q ha hb
    | true =>
      simp only [d256933, d258430, d259620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d256934 q = 1) (hb : d258431 q = 1) : d259621 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d256934, d258431, d259621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d256934, d258431, d259621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d256935 q = 1) (hb : d258432 q = 1) : d259622 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d256935, d258432, d259622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d256935, d258432, d259622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d256936 q = 1) (hb : d258433 q = 1) : d259623 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d256936, d258433, d259623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d256936, d258433, d259623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d256962 q = 1) (hb : d258459 q = 1) : d259649 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d256962, d258459, d259649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d256962, d258459, d259649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d256963 q = 1) (hb : d258460 q = 1) : d259650 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d256963, d258460, d259650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d256963, d258460, d259650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro64271 (p : Pattern) (ha : d256965 p = 1) (hb : d258462 p = 1) : d259652 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d256933 q = 1) (hb : d258430 q = 1) : d259620 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d256933, d258430, d259620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64263 q ha hb
    | true =>
      simp only [d256933, d258430, d259620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d256934 q = 1) (hb : d258431 q = 1) : d259621 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d256934, d258431, d259621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d256934, d258431, d259621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d256939 q = 1) (hb : d258436 q = 1) : d259626 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d256939, d258436, d259626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d256939, d258436, d259626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d256940 q = 1) (hb : d258437 q = 1) : d259627 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d256940, d258437, d259627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d256940, d258437, d259627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d256964 q = 1) (hb : d258461 q = 1) : d259651 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d256964, d258461, d259651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d256964, d258461, d259651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d256965 q = 1) (hb : d258462 q = 1) : d259652 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d256965, d258462, d259652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d256965, d258462, d259652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro64272 (p : Pattern) (ha : d256972 p = 1) (hb : d258469 p = 1) : d259659 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d256929 q = 1) (hb : d258426 q = 1) : d259616 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d256929, d258426, d259616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64262 q ha hb
    | true =>
      simp only [d256929, d258426, d259616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d256930 q = 1) (hb : d258427 q = 1) : d259617 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d256930, d258427, d259617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d256930, d258427, d259617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d256933 q = 1) (hb : d258430 q = 1) : d259620 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d256933, d258430, d259620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64263 q ha hb
    | true =>
      simp only [d256933, d258430, d259620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d256934 q = 1) (hb : d258431 q = 1) : d259621 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d256934, d258431, d259621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d256934, d258431, d259621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d256935 q = 1) (hb : d258432 q = 1) : d259622 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d256935, d258432, d259622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d256935, d258432, d259622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d256970 q = 1) (hb : d258467 q = 1) : d259657 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d256970, d258467, d259657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d256970, d258467, d259657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d256971 q = 1) (hb : d258468 q = 1) : d259658 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d256971, d258468, d259658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d256971, d258468, d259658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d256972 q = 1) (hb : d258469 q = 1) : d259659 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d256972, d258469, d259659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d256972, d258469, d259659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro64273 (p : Pattern) (ha : d256975 p = 1) (hb : d258472 p = 1) : d259662 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d256933 q = 1) (hb : d258430 q = 1) : d259620 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d256933, d258430, d259620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64263 q ha hb
    | true =>
      simp only [d256933, d258430, d259620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d256934 q = 1) (hb : d258431 q = 1) : d259621 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d256934, d258431, d259621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d256934, d258431, d259621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d256939 q = 1) (hb : d258436 q = 1) : d259626 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d256939, d258436, d259626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d256939, d258436, d259626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d256973 q = 1) (hb : d258470 q = 1) : d259660 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d256973, d258470, d259660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d256973, d258470, d259660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d256974 q = 1) (hb : d258471 q = 1) : d259661 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d256974, d258471, d259661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d256974, d258471, d259661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d256975 q = 1) (hb : d258472 q = 1) : d259662 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d256975, d258472, d259662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d256975, d258472, d259662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro64274 (p : Pattern) (ha : d256917 p = 1) (hb : d258481 p = 1) : d259670 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d256904 q = 1) (hb : d258392 q = 1) : d259582 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d256904, d258392, d259582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64256 q ha hb
    | true =>
      simp only [d256904, d258392, d259582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d256905 q = 1) (hb : d258393 q = 1) : d259583 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d256905, d258393, d259583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d256905, d258393, d259583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d256906 q = 1) (hb : d258394 q = 1) : d259584 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d256906, d258394, d259584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d256906, d258394, d259584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d256907 q = 1) (hb : d258395 q = 1) : d259585 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d256907, d258395, d259585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d256907, d258395, d259585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d256910 q = 1) (hb : d258398 q = 1) : d259588 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d256910, d258398, d259588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64257 q ha hb
    | true =>
      simp only [d256910, d258398, d259588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d256911 q = 1) (hb : d258399 q = 1) : d259589 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d256911, d258399, d259589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d256911, d258399, d259589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d256912 q = 1) (hb : d258400 q = 1) : d259590 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d256912, d258400, d259590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d256912, d258400, d259590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d256913 q = 1) (hb : d258401 q = 1) : d259591 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d256913, d258401, d259591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d256913, d258401, d259591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d256914 q = 1) (hb : d258402 q = 1) : d259592 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d256914, d258402, d259592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d256914, d258402, d259592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d256916 q = 1) (hb : d258412 q = 1) : d259602 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d256916, d258412, d259602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d256916, d258412, d259602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d256917 q = 1) (hb : d258481 q = 1) : d259670 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d256917, d258481, d259670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d256917, d258481, d259670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro64275 (p : Pattern) (ha : d256979 p = 1) (hb : d258477 p = 1) : d259666 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d258476 q = 1) : d258476 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d258189 q = 1) : d258189 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d256904 q = 1) (hb : d258392 q = 1) : d259582 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d256904, d258392, d259582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64256 q ha hb
    | true =>
      simp only [d256904, d258392, d259582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d256905 q = 1) (hb : d258393 q = 1) : d259583 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d256905, d258393, d259583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d256905, d258393, d259583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h5 (q : Pattern) (ha : d256906 q = 1) (hb : d258394 q = 1) : d259584 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d256906, d258394, d259584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d256906, d258394, d259584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d256907 q = 1) (hb : d258395 q = 1) : d259585 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d256907, d258395, d259585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d256907, d258395, d259585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h7 (q : Pattern) (ha : d256908 q = 1) (hb : d258396 q = 1) : d259586 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d256908, d258396, d259586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d256908, d258396, d259586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d256979 q = 1) (hb : d258477 q = 1) : d259666 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d256979, d258477, d259666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d256979, d258477, d259666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro64276 (p : Pattern) (ha : d256985 p = 1) (hb : d258487 p = 1) : d259676 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d256980 q = 1) (hb : d258478 q = 1) : d259667 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d256980, d258478, d259667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64275 q ha hb
    | true =>
      simp only [d256980, d258478, d259667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64258 q ha hb
  have h2 (q : Pattern) (ha : d256981 q = 1) (hb : d258479 q = 1) : d259668 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d256981, d258479, d259668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d256981, d258479, d259668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d256982 q = 1) (hb : d258480 q = 1) : d259669 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d256982, d258480, d259669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d256982, d258480, d259669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d256918 q = 1) (hb : d258482 q = 1) : d259671 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d256918, d258482, d259671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64258 q ha hb
    | true =>
      simp only [d256918, d258482, d259671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64274 q ha hb
  have h5 (q : Pattern) (ha : d256919 q = 1) (hb : d258483 q = 1) : d259672 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d256919, d258483, d259672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d256919, d258483, d259672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d256920 q = 1) (hb : d258484 q = 1) : d259673 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d256920, d258484, d259673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d256920, d258484, d259673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d256983 q = 1) (hb : d258485 q = 1) : d259674 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d256983, d258485, d259674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d256983, d258485, d259674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d256918 q = 1) (hb : d258414 q = 1) : d259604 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d256918, d258414, d259604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64258 q ha hb
    | true =>
      simp only [d256918, d258414, d259604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64260 q ha hb
  have h9 (q : Pattern) (ha : d256919 q = 1) (hb : d258415 q = 1) : d259605 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d256919, d258415, d259605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d256919, d258415, d259605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d256920 q = 1) (hb : d258416 q = 1) : d259606 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d256920, d258416, d259606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d256920, d258416, d259606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d256922 q = 1) (hb : d258419 q = 1) : d259609 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d256922, d258419, d259609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64260 q ha hb
    | true =>
      simp only [d256922, d258419, d259609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64261 q ha hb
  have h12 (q : Pattern) (ha : d256923 q = 1) (hb : d258420 q = 1) : d259610 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d256923, d258420, d259610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d256923, d258420, d259610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d256924 q = 1) (hb : d258421 q = 1) : d259611 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d256924, d258421, d259611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d256924, d258421, d259611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d256925 q = 1) (hb : d258422 q = 1) : d259612 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d256925, d258422, d259612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d256925, d258422, d259612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d256984 q = 1) (hb : d258486 q = 1) : d259675 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d256984, d258486, d259675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d256984, d258486, d259675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d256985 q = 1) (hb : d258487 q = 1) : d259676 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d256985, d258487, d259676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d256985, d258487, d259676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h16 p ha hb
theorem andIntro64277 (p : Pattern) (ha : d256991 p = 1) (hb : d258493 p = 1) : d259682 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d256986 q = 1) (hb : d258488 q = 1) : d259677 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d256986, d258488, d259677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64276 q ha hb
    | true =>
      simp only [d256986, d258488, d259677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d256987 q = 1) (hb : d258489 q = 1) : d259678 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d256987, d258489, d259678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d256987, d258489, d259678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d256929 q = 1) (hb : d258426 q = 1) : d259616 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d256929, d258426, d259616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64262 q ha hb
    | true =>
      simp only [d256929, d258426, d259616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d256930 q = 1) (hb : d258427 q = 1) : d259617 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d256930, d258427, d259617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d256930, d258427, d259617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d256988 q = 1) (hb : d258490 q = 1) : d259679 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d256988, d258490, d259679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d256988, d258490, d259679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d256989 q = 1) (hb : d258491 q = 1) : d259680 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d256989, d258491, d259680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d256989, d258491, d259680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d256990 q = 1) (hb : d258492 q = 1) : d259681 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d256990, d258492, d259681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d256990, d258492, d259681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d256991 q = 1) (hb : d258493 q = 1) : d259682 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d256991, d258493, d259682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d256991, d258493, d259682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro64278 (p : Pattern) (ha : d256997 p = 1) (hb : d258499 p = 1) : d259688 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d256929 q = 1) (hb : d258426 q = 1) : d259616 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d256929, d258426, d259616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64262 q ha hb
    | true =>
      simp only [d256929, d258426, d259616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d256930 q = 1) (hb : d258427 q = 1) : d259617 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d256930, d258427, d259617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d256930, d258427, d259617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d256994 q = 1) (hb : d258496 q = 1) : d259685 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d256994, d258496, d259685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d256994, d258496, d259685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d256995 q = 1) (hb : d258497 q = 1) : d259686 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d256995, d258497, d259686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d256995, d258497, d259686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d256996 q = 1) (hb : d258498 q = 1) : d259687 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d256996, d258498, d259687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d256996, d258498, d259687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d256997 q = 1) (hb : d258499 q = 1) : d259688 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d256997, d258499, d259688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d256997, d258499, d259688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro64279 (p : Pattern) (ha : d257003 p = 1) (hb : d258505 p = 1) : d259694 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d256966 q = 1) (hb : d258463 q = 1) : d259653 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d256966, d258463, d259653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64270 q ha hb
    | true =>
      simp only [d256966, d258463, d259653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64271 q ha hb
  have h2 (q : Pattern) (ha : d256967 q = 1) (hb : d258464 q = 1) : d259654 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d256967, d258464, d259654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d256967, d258464, d259654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d256968 q = 1) (hb : d258465 q = 1) : d259655 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d256968, d258465, d259655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d256968, d258465, d259655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d256969 q = 1) (hb : d258466 q = 1) : d259656 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d256969, d258466, d259656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d256969, d258466, d259656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d256976 q = 1) (hb : d258473 q = 1) : d259663 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d256976, d258473, d259663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64272 q ha hb
    | true =>
      simp only [d256976, d258473, d259663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64273 q ha hb
  have h6 (q : Pattern) (ha : d256977 q = 1) (hb : d258474 q = 1) : d259664 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d256977, d258474, d259664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d256977, d258474, d259664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d256978 q = 1) (hb : d258475 q = 1) : d259665 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d256978, d258475, d259665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d256978, d258475, d259665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d256992 q = 1) (hb : d258494 q = 1) : d259683 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d256992, d258494, d259683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64277 q ha hb
    | true =>
      simp only [d256992, d258494, d259683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64264 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d256943 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d256993 q = 1) (hb : d258495 q = 1) : d259684 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d256993, d258495, d259684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d256993, d258495, d259684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d256998 q = 1) (hb : d258500 q = 1) : d259689 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d256998, d258500, d259689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64278 q ha hb
    | true =>
      simp only [d256998, d258500, d259689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d256999 q = 1) (hb : d258501 q = 1) : d259690 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d256999, d258501, d259690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d256999, d258501, d259690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d257000 q = 1) (hb : d258502 q = 1) : d259691 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d257000, d258502, d259691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d257000, d258502, d259691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d257001 q = 1) (hb : d258503 q = 1) : d259692 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d257001, d258503, d259692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d257001, d258503, d259692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d257002 q = 1) (hb : d258504 q = 1) : d259693 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d257002, d258504, d259693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d257002, d258504, d259693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d257003 q = 1) (hb : d258505 q = 1) : d259694 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d257003, d258505, d259694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d257003, d258505, d259694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro64280 (p : Pattern) (ha : d257004 p = 1) (hb : d258506 p = 1) : d259695 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d256929 q = 1) (hb : d258426 q = 1) : d259616 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d256929, d258426, d259616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64262 q ha hb
    | true =>
      simp only [d256929, d258426, d259616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d256930 q = 1) (hb : d258427 q = 1) : d259617 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d256930, d258427, d259617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d256930, d258427, d259617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d256933 q = 1) (hb : d258430 q = 1) : d259620 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d256933, d258430, d259620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64263 q ha hb
    | true =>
      simp only [d256933, d258430, d259620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d256934 q = 1) (hb : d258431 q = 1) : d259621 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d256934, d258431, d259621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d256934, d258431, d259621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d256935 q = 1) (hb : d258432 q = 1) : d259622 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d256935, d258432, d259622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d256935, d258432, d259622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d256936 q = 1) (hb : d258433 q = 1) : d259623 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d256936, d258433, d259623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d256936, d258433, d259623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d256962 q = 1) (hb : d258459 q = 1) : d259649 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d256962, d258459, d259649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d256962, d258459, d259649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d257004 q = 1) (hb : d258506 q = 1) : d259695 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d257004, d258506, d259695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d257004, d258506, d259695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro64281 (p : Pattern) (ha : d257005 p = 1) (hb : d258507 p = 1) : d259696 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d256933 q = 1) (hb : d258430 q = 1) : d259620 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d256933, d258430, d259620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64263 q ha hb
    | true =>
      simp only [d256933, d258430, d259620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d256934 q = 1) (hb : d258431 q = 1) : d259621 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d256934, d258431, d259621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d256934, d258431, d259621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d256939 q = 1) (hb : d258436 q = 1) : d259626 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d256939, d258436, d259626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d256939, d258436, d259626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d256940 q = 1) (hb : d258437 q = 1) : d259627 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d256940, d258437, d259627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d256940, d258437, d259627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d256964 q = 1) (hb : d258461 q = 1) : d259651 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d256964, d258461, d259651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d256964, d258461, d259651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d257005 q = 1) (hb : d258507 q = 1) : d259696 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d257005, d258507, d259696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d257005, d258507, d259696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro64282 (p : Pattern) (ha : d257010 p = 1) (hb : d258512 p = 1) : d259701 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d256929 q = 1) (hb : d258426 q = 1) : d259616 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d256929, d258426, d259616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64262 q ha hb
    | true =>
      simp only [d256929, d258426, d259616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d256930 q = 1) (hb : d258427 q = 1) : d259617 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d256930, d258427, d259617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d256930, d258427, d259617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d256933 q = 1) (hb : d258430 q = 1) : d259620 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d256933, d258430, d259620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64263 q ha hb
    | true =>
      simp only [d256933, d258430, d259620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d256934 q = 1) (hb : d258431 q = 1) : d259621 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d256934, d258431, d259621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d256934, d258431, d259621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d256935 q = 1) (hb : d258432 q = 1) : d259622 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d256935, d258432, d259622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d256935, d258432, d259622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d256970 q = 1) (hb : d258467 q = 1) : d259657 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d256970, d258467, d259657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d256970, d258467, d259657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d256971 q = 1) (hb : d258468 q = 1) : d259658 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d256971, d258468, d259658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d256971, d258468, d259658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d257010 q = 1) (hb : d258512 q = 1) : d259701 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d257010, d258512, d259701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d257010, d258512, d259701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro64283 (p : Pattern) (ha : d257011 p = 1) (hb : d258513 p = 1) : d259702 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d256933 q = 1) (hb : d258430 q = 1) : d259620 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d256933, d258430, d259620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64263 q ha hb
    | true =>
      simp only [d256933, d258430, d259620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d256934 q = 1) (hb : d258431 q = 1) : d259621 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d256934, d258431, d259621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d256934, d258431, d259621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d256939 q = 1) (hb : d258436 q = 1) : d259626 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d256939, d258436, d259626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d256939, d258436, d259626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d256973 q = 1) (hb : d258470 q = 1) : d259660 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d256973, d258470, d259660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d256973, d258470, d259660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d256974 q = 1) (hb : d258471 q = 1) : d259661 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d256974, d258471, d259661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d256974, d258471, d259661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d257011 q = 1) (hb : d258513 q = 1) : d259702 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d257011, d258513, d259702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d257011, d258513, d259702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro64284 (p : Pattern) (ha : d257015 p = 1) (hb : d258517 p = 1) : d259706 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d256986 q = 1) (hb : d258488 q = 1) : d259677 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d256986, d258488, d259677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64276 q ha hb
    | true =>
      simp only [d256986, d258488, d259677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d256987 q = 1) (hb : d258489 q = 1) : d259678 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d256987, d258489, d259678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d256987, d258489, d259678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d256929 q = 1) (hb : d258426 q = 1) : d259616 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d256929, d258426, d259616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64262 q ha hb
    | true =>
      simp only [d256929, d258426, d259616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d256930 q = 1) (hb : d258427 q = 1) : d259617 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d256930, d258427, d259617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d256930, d258427, d259617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d256988 q = 1) (hb : d258490 q = 1) : d259679 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d256988, d258490, d259679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d256988, d258490, d259679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d256989 q = 1) (hb : d258491 q = 1) : d259680 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d256989, d258491, d259680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d256989, d258491, d259680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d256990 q = 1) (hb : d258492 q = 1) : d259681 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d256990, d258492, d259681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d256990, d258492, d259681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d257015 q = 1) (hb : d258517 q = 1) : d259706 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d257015, d258517, d259706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d257015, d258517, d259706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro64285 (p : Pattern) (ha : d257018 p = 1) (hb : d258520 p = 1) : d259709 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d256929 q = 1) (hb : d258426 q = 1) : d259616 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d256929, d258426, d259616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64262 q ha hb
    | true =>
      simp only [d256929, d258426, d259616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d256930 q = 1) (hb : d258427 q = 1) : d259617 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d256930, d258427, d259617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d256930, d258427, d259617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d256994 q = 1) (hb : d258496 q = 1) : d259685 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d256994, d258496, d259685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d256994, d258496, d259685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d256995 q = 1) (hb : d258497 q = 1) : d259686 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d256995, d258497, d259686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d256995, d258497, d259686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d256996 q = 1) (hb : d258498 q = 1) : d259687 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d256996, d258498, d259687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d256996, d258498, d259687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d257018 q = 1) (hb : d258520 q = 1) : d259709 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d257018, d258520, d259709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d257018, d258520, d259709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro64286 (p : Pattern) (ha : d257024 p = 1) (hb : d258526 p = 1) : d259715 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d256966 q = 1) (hb : d258463 q = 1) : d259653 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d256966, d258463, d259653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64270 q ha hb
    | true =>
      simp only [d256966, d258463, d259653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64271 q ha hb
  have h2 (q : Pattern) (ha : d256967 q = 1) (hb : d258464 q = 1) : d259654 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d256967, d258464, d259654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d256967, d258464, d259654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d256968 q = 1) (hb : d258465 q = 1) : d259655 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d256968, d258465, d259655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d256968, d258465, d259655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d256969 q = 1) (hb : d258466 q = 1) : d259656 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d256969, d258466, d259656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d256969, d258466, d259656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d256976 q = 1) (hb : d258473 q = 1) : d259663 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d256976, d258473, d259663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64272 q ha hb
    | true =>
      simp only [d256976, d258473, d259663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64273 q ha hb
  have h6 (q : Pattern) (ha : d256977 q = 1) (hb : d258474 q = 1) : d259664 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d256977, d258474, d259664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d256977, d258474, d259664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d256978 q = 1) (hb : d258475 q = 1) : d259665 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d256978, d258475, d259665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d256978, d258475, d259665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d256992 q = 1) (hb : d258494 q = 1) : d259683 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d256992, d258494, d259683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64277 q ha hb
    | true =>
      simp only [d256992, d258494, d259683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64264 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d256943 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d256993 q = 1) (hb : d258495 q = 1) : d259684 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d256993, d258495, d259684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d256993, d258495, d259684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d256998 q = 1) (hb : d258500 q = 1) : d259689 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d256998, d258500, d259689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64278 q ha hb
    | true =>
      simp only [d256998, d258500, d259689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d256999 q = 1) (hb : d258501 q = 1) : d259690 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d256999, d258501, d259690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d256999, d258501, d259690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d257000 q = 1) (hb : d258502 q = 1) : d259691 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d257000, d258502, d259691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d257000, d258502, d259691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d257001 q = 1) (hb : d258503 q = 1) : d259692 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d257001, d258503, d259692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d257001, d258503, d259692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d257002 q = 1) (hb : d258504 q = 1) : d259693 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d257002, d258504, d259693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d257002, d258504, d259693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d257006 q = 1) (hb : d258508 q = 1) : d259697 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d257006, d258508, d259697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64280 q ha hb
    | true =>
      simp only [d257006, d258508, d259697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64281 q ha hb
  have h17 (q : Pattern) (ha : d257007 q = 1) (hb : d258509 q = 1) : d259698 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d257007, d258509, d259698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d257007, d258509, d259698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d257008 q = 1) (hb : d258510 q = 1) : d259699 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d257008, d258510, d259699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d257008, d258510, d259699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d257009 q = 1) (hb : d258511 q = 1) : d259700 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d257009, d258511, d259700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d257009, d258511, d259700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d257012 q = 1) (hb : d258514 q = 1) : d259703 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d257012, d258514, d259703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64282 q ha hb
    | true =>
      simp only [d257012, d258514, d259703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64283 q ha hb
  have h21 (q : Pattern) (ha : d257013 q = 1) (hb : d258515 q = 1) : d259704 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d257013, d258515, d259704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d257013, d258515, d259704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d257014 q = 1) (hb : d258516 q = 1) : d259705 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d257014, d258516, d259705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d257014, d258516, d259705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d257016 q = 1) (hb : d258518 q = 1) : d259707 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d257016, d258518, d259707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64284 q ha hb
    | true =>
      simp only [d257016, d258518, d259707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64267 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d256953 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d257017 q = 1) (hb : d258519 q = 1) : d259708 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d257017, d258519, d259708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d257017, d258519, d259708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d257019 q = 1) (hb : d258521 q = 1) : d259710 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d257019, d258521, d259710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64285 q ha hb
    | true =>
      simp only [d257019, d258521, d259710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d257020 q = 1) (hb : d258522 q = 1) : d259711 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d257020, d258522, d259711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d257020, d258522, d259711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d257021 q = 1) (hb : d258523 q = 1) : d259712 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d257021, d258523, d259712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d257021, d258523, d259712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d257022 q = 1) (hb : d258524 q = 1) : d259713 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d257022, d258524, d259713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d257022, d258524, d259713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d257023 q = 1) (hb : d258525 q = 1) : d259714 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d257023, d258525, d259714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d257023, d258525, d259714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d257024 q = 1) (hb : d258526 q = 1) : d259715 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d257024, d258526, d259715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d257024, d258526, d259715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro64287 (p : Pattern) (ha : d257031 p = 1) (hb : d258533 p = 1) : d259722 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d256943 q = 1) (hb : d258440 q = 1) : d259630 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d256943, d258440, d259630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64264 q ha hb
    | true =>
      simp only [d256943, d258440, d259630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64265 q ha hb
  have h2 (q : Pattern) (ha : d256944 q = 1) (hb : d258441 q = 1) : d259631 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d256944, d258441, d259631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d256944, d258441, d259631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d256945 q = 1) (hb : d258442 q = 1) : d259632 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d256945, d258442, d259632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d256945, d258442, d259632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d256946 q = 1) (hb : d258443 q = 1) : d259633 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d256946, d258443, d259633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d256946, d258443, d259633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d256947 q = 1) (hb : d258444 q = 1) : d259634 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d256947, d258444, d259634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d256947, d258444, d259634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d257026 q = 1) (hb : d258528 q = 1) : d259717 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d257026, d258528, d259717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64265 q ha hb
    | true =>
      simp only [d257026, d258528, d259717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d257027 q = 1) (hb : d258529 q = 1) : d259718 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d257027, d258529, d259718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d257027, d258529, d259718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d257028 q = 1) (hb : d258530 q = 1) : d259719 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d257028, d258530, d259719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d257028, d258530, d259719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d257029 q = 1) (hb : d258531 q = 1) : d259720 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d257029, d258531, d259720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d257029, d258531, d259720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d257030 q = 1) (hb : d258532 q = 1) : d259721 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d257030, d258532, d259721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d257030, d258532, d259721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d257031 q = 1) (hb : d258533 q = 1) : d259722 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d257031, d258533, d259722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d257031, d258533, d259722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro64288 (p : Pattern) (ha : d257037 p = 1) (hb : d258539 p = 1) : d259728 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d257026 q = 1) (hb : d258528 q = 1) : d259717 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d257026, d258528, d259717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64265 q ha hb
    | true =>
      simp only [d257026, d258528, d259717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d257027 q = 1) (hb : d258529 q = 1) : d259718 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d257027, d258529, d259718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d257027, d258529, d259718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d257028 q = 1) (hb : d258530 q = 1) : d259719 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d257028, d258530, d259719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d257028, d258530, d259719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d257029 q = 1) (hb : d258531 q = 1) : d259720 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d257029, d258531, d259720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d257029, d258531, d259720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d257030 q = 1) (hb : d258532 q = 1) : d259721 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d257030, d258532, d259721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d257030, d258532, d259721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d257032 q = 1) (hb : d258534 q = 1) : d259723 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d257032, d258534, d259723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64268 q ha hb
    | true =>
      simp only [d257032, d258534, d259723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d257033 q = 1) (hb : d258535 q = 1) : d259724 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d257033, d258535, d259724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d257033, d258535, d259724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d257034 q = 1) (hb : d258536 q = 1) : d259725 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d257034, d258536, d259725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d257034, d258536, d259725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d257035 q = 1) (hb : d258537 q = 1) : d259726 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d257035, d258537, d259726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d257035, d258537, d259726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d257036 q = 1) (hb : d258538 q = 1) : d259727 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d257036, d258538, d259727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d257036, d258538, d259727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d257037 q = 1) (hb : d258539 q = 1) : d259728 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d257037, d258539, d259728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d257037, d258539, d259728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro64289 (p : Pattern) (ha : d257044 p = 1) (hb : d258546 p = 1) : d259735 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d257016 q = 1) (hb : d258518 q = 1) : d259707 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d257016, d258518, d259707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64284 q ha hb
    | true =>
      simp only [d257016, d258518, d259707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64267 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d256953 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d257017 q = 1) (hb : d258519 q = 1) : d259708 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d257017, d258519, d259708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d257017, d258519, d259708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d257019 q = 1) (hb : d258521 q = 1) : d259710 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d257019, d258521, d259710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64285 q ha hb
    | true =>
      simp only [d257019, d258521, d259710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d257020 q = 1) (hb : d258522 q = 1) : d259711 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d257020, d258522, d259711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d257020, d258522, d259711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d257021 q = 1) (hb : d258523 q = 1) : d259712 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d257021, d258523, d259712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d257021, d258523, d259712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d257042 q = 1) (hb : d258544 q = 1) : d259733 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d257042, d258544, d259733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d257042, d258544, d259733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d257043 q = 1) (hb : d258545 q = 1) : d259734 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d257043, d258545, d259734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d257043, d258545, d259734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d257044 q = 1) (hb : d258546 q = 1) : d259735 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d257044, d258546, d259735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d257044, d258546, d259735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro64290 (p : Pattern) (ha : d257046 p = 1) (hb : d258548 p = 1) : d259737 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d257032 q = 1) (hb : d258534 q = 1) : d259723 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d257032, d258534, d259723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64268 q ha hb
    | true =>
      simp only [d257032, d258534, d259723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d257033 q = 1) (hb : d258535 q = 1) : d259724 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d257033, d258535, d259724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d257033, d258535, d259724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d257034 q = 1) (hb : d258536 q = 1) : d259725 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d257034, d258536, d259725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d257034, d258536, d259725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d257035 q = 1) (hb : d258537 q = 1) : d259726 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d257035, d258537, d259726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d257035, d258537, d259726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d257036 q = 1) (hb : d258538 q = 1) : d259727 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d257036, d258538, d259727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d257036, d258538, d259727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d257046 q = 1) (hb : d258548 q = 1) : d259737 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d257046, d258548, d259737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d257046, d258548, d259737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro64291 (p : Pattern) (ha : d257057 p = 1) (hb : d258560 p = 1) : d259748 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d258554 q = 1) : d258554 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d258277 q = 1) : d258277 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d257052 q = 1) (hb : d258555 q = 1) : d259743 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d257052, d258555, d259743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d257052, d258555, d259743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64256 q ha hb
  have h4 (q : Pattern) (ha : d256904 q = 1) (hb : d258392 q = 1) : d259582 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d256904, d258392, d259582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64256 q ha hb
    | true =>
      simp only [d256904, d258392, d259582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h5 (q : Pattern) (ha : d257053 q = 1) (hb : d258556 q = 1) : d259744 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d257053, d258556, d259744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d257053, d258556, d259744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d256905 q = 1) (hb : d258393 q = 1) : d259583 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d256905, d258393, d259583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d256905, d258393, d259583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h7 (q : Pattern) (ha : d257054 q = 1) (hb : d258557 q = 1) : d259745 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d257054, d258557, d259745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d257054, d258557, d259745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d257055 q = 1) (hb : d258558 q = 1) : d259746 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d257055, d258558, d259746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d257055, d258558, d259746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h9 (q : Pattern) (ha : d257056 q = 1) (hb : d258559 q = 1) : d259747 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d257056, d258559, d259747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d257056, d258559, d259747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d257057 q = 1) (hb : d258560 q = 1) : d259748 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d257057, d258560, d259748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d257057, d258560, d259748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro64292 (p : Pattern) (ha : d257063 p = 1) (hb : d258566 p = 1) : d259754 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d258277 q = 1) : d258277 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d257052 q = 1) (hb : d258555 q = 1) : d259743 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d257052, d258555, d259743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d257052, d258555, d259743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64256 q ha hb
  have h3 (q : Pattern) (ha : d256904 q = 1) (hb : d258392 q = 1) : d259582 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d256904, d258392, d259582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64256 q ha hb
    | true =>
      simp only [d256904, d258392, d259582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h4 (q : Pattern) (ha : d257053 q = 1) (hb : d258556 q = 1) : d259744 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d257053, d258556, d259744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d257053, d258556, d259744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d256905 q = 1) (hb : d258393 q = 1) : d259583 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d256905, d258393, d259583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d256905, d258393, d259583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h6 (q : Pattern) (ha : d257054 q = 1) (hb : d258557 q = 1) : d259745 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d257054, d258557, d259745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d257054, d258557, d259745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d257055 q = 1) (hb : d258558 q = 1) : d259746 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d257055, d258558, d259746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d257055, d258558, d259746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h8 (q : Pattern) (ha : d257056 q = 1) (hb : d258559 q = 1) : d259747 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d257056, d258559, d259747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d257056, d258559, d259747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d257058 q = 1) (hb : d258561 q = 1) : d259749 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d257058, d258561, d259749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d257058, d258561, d259749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64257 q ha hb
  have h10 (q : Pattern) (ha : d256910 q = 1) (hb : d258398 q = 1) : d259588 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d256910, d258398, d259588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64257 q ha hb
    | true =>
      simp only [d256910, d258398, d259588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h11 (q : Pattern) (ha : d257059 q = 1) (hb : d258562 q = 1) : d259750 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d257059, d258562, d259750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d257059, d258562, d259750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d256911 q = 1) (hb : d258399 q = 1) : d259589 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d256911, d258399, d259589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d256911, d258399, d259589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h13 (q : Pattern) (ha : d257060 q = 1) (hb : d258563 q = 1) : d259751 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d257060, d258563, d259751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d257060, d258563, d259751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d257061 q = 1) (hb : d258564 q = 1) : d259752 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d257061, d258564, d259752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d257061, d258564, d259752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h15 (q : Pattern) (ha : d257062 q = 1) (hb : d258565 q = 1) : d259753 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d257062, d258565, d259753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d257062, d258565, d259753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d257063 q = 1) (hb : d258566 q = 1) : d259754 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d257063, d258566, d259754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d257063, d258566, d259754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro64293 (p : Pattern) (ha : d257068 p = 1) (hb : d258571 p = 1) : d259759 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d257052 q = 1) (hb : d258555 q = 1) : d259743 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d257052, d258555, d259743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d257052, d258555, d259743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64256 q ha hb
  have h2 (q : Pattern) (ha : d256904 q = 1) (hb : d258392 q = 1) : d259582 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d256904, d258392, d259582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64256 q ha hb
    | true =>
      simp only [d256904, d258392, d259582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d257053 q = 1) (hb : d258556 q = 1) : d259744 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d257053, d258556, d259744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d257053, d258556, d259744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d256905 q = 1) (hb : d258393 q = 1) : d259583 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d256905, d258393, d259583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d256905, d258393, d259583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d257054 q = 1) (hb : d258557 q = 1) : d259745 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d257054, d258557, d259745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d257054, d258557, d259745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d257055 q = 1) (hb : d258558 q = 1) : d259746 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d257055, d258558, d259746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d257055, d258558, d259746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d257058 q = 1) (hb : d258561 q = 1) : d259749 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d257058, d258561, d259749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d257058, d258561, d259749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64257 q ha hb
  have h8 (q : Pattern) (ha : d256910 q = 1) (hb : d258398 q = 1) : d259588 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d256910, d258398, d259588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64257 q ha hb
    | true =>
      simp only [d256910, d258398, d259588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d257059 q = 1) (hb : d258562 q = 1) : d259750 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d257059, d258562, d259750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d257059, d258562, d259750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d256911 q = 1) (hb : d258399 q = 1) : d259589 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d256911, d258399, d259589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d256911, d258399, d259589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d257060 q = 1) (hb : d258563 q = 1) : d259751 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d257060, d258563, d259751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d257060, d258563, d259751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d257061 q = 1) (hb : d258564 q = 1) : d259752 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d257061, d258564, d259752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d257061, d258564, d259752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d257062 q = 1) (hb : d258565 q = 1) : d259753 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d257062, d258565, d259753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d257062, d258565, d259753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d257067 q = 1) (hb : d258570 q = 1) : d259758 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d257067, d258570, d259758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d257067, d258570, d259758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d257068 q = 1) (hb : d258571 q = 1) : d259759 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d257068, d258571, d259759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d257068, d258571, d259759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro64294 (p : Pattern) (ha : d257068 p = 1) (hb : d258581 p = 1) : d259769 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d257052 q = 1) (hb : d258555 q = 1) : d259743 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d257052, d258555, d259743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d257052, d258555, d259743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64256 q ha hb
  have h2 (q : Pattern) (ha : d256904 q = 1) (hb : d258392 q = 1) : d259582 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d256904, d258392, d259582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64256 q ha hb
    | true =>
      simp only [d256904, d258392, d259582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d257053 q = 1) (hb : d258556 q = 1) : d259744 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d257053, d258556, d259744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d257053, d258556, d259744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d256905 q = 1) (hb : d258393 q = 1) : d259583 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d256905, d258393, d259583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d256905, d258393, d259583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d257054 q = 1) (hb : d258557 q = 1) : d259745 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d257054, d258557, d259745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d257054, d258557, d259745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d257055 q = 1) (hb : d258558 q = 1) : d259746 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d257055, d258558, d259746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d257055, d258558, d259746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d257058 q = 1) (hb : d258576 q = 1) : d259764 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d257058, d258576, d259764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d257058, d258576, d259764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64259 q ha hb
  have h8 (q : Pattern) (ha : d256910 q = 1) (hb : d258407 q = 1) : d259597 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d256910, d258407, d259597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64259 q ha hb
    | true =>
      simp only [d256910, d258407, d259597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d257059 q = 1) (hb : d258577 q = 1) : d259765 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d257059, d258577, d259765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d257059, d258577, d259765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d256911 q = 1) (hb : d258408 q = 1) : d259598 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d256911, d258408, d259598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d256911, d258408, d259598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d257060 q = 1) (hb : d258578 q = 1) : d259766 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d257060, d258578, d259766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d257060, d258578, d259766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d257061 q = 1) (hb : d258579 q = 1) : d259767 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d257061, d258579, d259767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d257061, d258579, d259767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d257062 q = 1) (hb : d258580 q = 1) : d259768 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d257062, d258580, d259768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d257062, d258580, d259768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d257058 q = 1) (hb : d258561 q = 1) : d259749 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d257058, d258561, d259749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d257058, d258561, d259749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64257 q ha hb
  have h15 (q : Pattern) (ha : d256910 q = 1) (hb : d258398 q = 1) : d259588 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d256910, d258398, d259588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64257 q ha hb
    | true =>
      simp only [d256910, d258398, d259588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d257059 q = 1) (hb : d258562 q = 1) : d259750 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d257059, d258562, d259750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d257059, d258562, d259750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d256911 q = 1) (hb : d258399 q = 1) : d259589 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d256911, d258399, d259589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d256911, d258399, d259589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d257060 q = 1) (hb : d258563 q = 1) : d259751 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d257060, d258563, d259751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d257060, d258563, d259751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d257061 q = 1) (hb : d258564 q = 1) : d259752 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d257061, d258564, d259752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d257061, d258564, d259752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d257067 q = 1) (hb : d258570 q = 1) : d259758 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d257067, d258570, d259758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d257067, d258570, d259758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d257068 q = 1) (hb : d258581 q = 1) : d259769 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d257068, d258581, d259769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d257068, d258581, d259769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro64295 (p : Pattern) (ha : d257073 p = 1) (hb : d258586 p = 1) : d259774 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d257058 q = 1) (hb : d258576 q = 1) : d259764 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d257058, d258576, d259764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d257058, d258576, d259764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64259 q ha hb
  have h2 (q : Pattern) (ha : d256910 q = 1) (hb : d258407 q = 1) : d259597 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d256910, d258407, d259597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64259 q ha hb
    | true =>
      simp only [d256910, d258407, d259597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d257059 q = 1) (hb : d258577 q = 1) : d259765 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d257059, d258577, d259765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d257059, d258577, d259765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d256911 q = 1) (hb : d258408 q = 1) : d259598 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d256911, d258408, d259598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d256911, d258408, d259598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d257060 q = 1) (hb : d258578 q = 1) : d259766 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d257060, d258578, d259766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d257060, d258578, d259766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d257061 q = 1) (hb : d258579 q = 1) : d259767 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d257061, d258579, d259767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d257061, d258579, d259767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d257067 q = 1) (hb : d258585 q = 1) : d259773 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d257067, d258585, d259773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d257067, d258585, d259773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d257073 q = 1) (hb : d258586 q = 1) : d259774 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d257073, d258586, d259774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d257073, d258586, d259774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro64296 (p : Pattern) (ha : d257079 p = 1) (hb : d258592 p = 1) : d259780 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d257064 q = 1) (hb : d258567 q = 1) : d259755 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d257064, d258567, d259755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64291 q ha hb
    | true =>
      simp only [d257064, d258567, d259755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64292 q ha hb
  have h2 (q : Pattern) (ha : d257065 q = 1) (hb : d258568 q = 1) : d259756 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d257065, d258568, d259756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d257065, d258568, d259756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d257066 q = 1) (hb : d258569 q = 1) : d259757 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d257066, d258569, d259757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d257066, d258569, d259757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d257069 q = 1) (hb : d258572 q = 1) : d259760 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d257069, d258572, d259760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64292 q ha hb
    | true =>
      simp only [d257069, d258572, d259760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64293 q ha hb
  have h5 (q : Pattern) (ha : d257070 q = 1) (hb : d258573 q = 1) : d259761 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d257070, d258573, d259761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d257070, d258573, d259761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d257071 q = 1) (hb : d258574 q = 1) : d259762 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d257071, d258574, d259762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d257071, d258574, d259762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d257072 q = 1) (hb : d258575 q = 1) : d259763 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d257072, d258575, d259763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d257072, d258575, d259763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d257069 q = 1) (hb : d258582 q = 1) : d259770 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d257069, d258582, d259770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64292 q ha hb
    | true =>
      simp only [d257069, d258582, d259770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64294 q ha hb
  have h9 (q : Pattern) (ha : d257070 q = 1) (hb : d258583 q = 1) : d259771 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d257070, d258583, d259771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d257070, d258583, d259771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d257071 q = 1) (hb : d258584 q = 1) : d259772 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d257071, d258584, d259772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d257071, d258584, d259772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d257074 q = 1) (hb : d258587 q = 1) : d259775 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d257074, d258587, d259775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64294 q ha hb
    | true =>
      simp only [d257074, d258587, d259775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64295 q ha hb
  have h12 (q : Pattern) (ha : d257075 q = 1) (hb : d258588 q = 1) : d259776 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d257075, d258588, d259776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d257075, d258588, d259776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d257076 q = 1) (hb : d258589 q = 1) : d259777 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d257076, d258589, d259777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d257076, d258589, d259777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d257077 q = 1) (hb : d258590 q = 1) : d259778 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d257077, d258590, d259778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d257077, d258590, d259778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d257078 q = 1) (hb : d258591 q = 1) : d259779 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d257078, d258591, d259779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d257078, d258591, d259779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d257079 q = 1) (hb : d258592 q = 1) : d259780 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d257079, d258592, d259780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d257079, d258592, d259780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h16 p ha hb
theorem andIntro64297 (p : Pattern) (ha : d257084 p = 1) (hb : d258597 p = 1) : d259785 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d257069 q = 1) (hb : d258582 q = 1) : d259770 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d257069, d258582, d259770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64292 q ha hb
    | true =>
      simp only [d257069, d258582, d259770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64294 q ha hb
  have h2 (q : Pattern) (ha : d257070 q = 1) (hb : d258583 q = 1) : d259771 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d257070, d258583, d259771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d257070, d258583, d259771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d257071 q = 1) (hb : d258584 q = 1) : d259772 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d257071, d258584, d259772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d257071, d258584, d259772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d257074 q = 1) (hb : d258587 q = 1) : d259775 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d257074, d258587, d259775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64294 q ha hb
    | true =>
      simp only [d257074, d258587, d259775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64295 q ha hb
  have h5 (q : Pattern) (ha : d257075 q = 1) (hb : d258588 q = 1) : d259776 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d257075, d258588, d259776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d257075, d258588, d259776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d257076 q = 1) (hb : d258589 q = 1) : d259777 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d257076, d258589, d259777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d257076, d258589, d259777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d257077 q = 1) (hb : d258590 q = 1) : d259778 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d257077, d258590, d259778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d257077, d258590, d259778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d257082 q = 1) (hb : d258595 q = 1) : d259783 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d257082, d258595, d259783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d257082, d258595, d259783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d257083 q = 1) (hb : d258596 q = 1) : d259784 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d257083, d258596, d259784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d257083, d258596, d259784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d257084 q = 1) (hb : d258597 q = 1) : d259785 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d257084, d258597, d259785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d257084, d258597, d259785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro64298 (p : Pattern) (ha : d257090 p = 1) (hb : d258603 p = 1) : d259791 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d257080 q = 1) (hb : d258593 q = 1) : d259781 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d257080, d258593, d259781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64296 q ha hb
    | true =>
      simp only [d257080, d258593, d259781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d257081 q = 1) (hb : d258594 q = 1) : d259782 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d257081, d258594, d259782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d257081, d258594, d259782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d257085 q = 1) (hb : d258598 q = 1) : d259786 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d257085, d258598, d259786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64297 q ha hb
    | true =>
      simp only [d257085, d258598, d259786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d257086 q = 1) (hb : d258599 q = 1) : d259787 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d257086, d258599, d259787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d257086, d258599, d259787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d257087 q = 1) (hb : d258600 q = 1) : d259788 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d257087, d258600, d259788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d257087, d258600, d259788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d257088 q = 1) (hb : d258601 q = 1) : d259789 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d257088, d258601, d259789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d257088, d258601, d259789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d257089 q = 1) (hb : d258602 q = 1) : d259790 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d257089, d258602, d259790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d257089, d258602, d259790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d257090 q = 1) (hb : d258603 q = 1) : d259791 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d257090, d258603, d259791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d257090, d258603, d259791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro64299 (p : Pattern) (ha : d257092 p = 1) (hb : d258605 p = 1) : d259793 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d257074 q = 1) (hb : d258587 q = 1) : d259775 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d257074, d258587, d259775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64294 q ha hb
    | true =>
      simp only [d257074, d258587, d259775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64295 q ha hb
  have h2 (q : Pattern) (ha : d257075 q = 1) (hb : d258588 q = 1) : d259776 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d257075, d258588, d259776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d257075, d258588, d259776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d257076 q = 1) (hb : d258589 q = 1) : d259777 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d257076, d258589, d259777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d257076, d258589, d259777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d257082 q = 1) (hb : d258595 q = 1) : d259783 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d257082, d258595, d259783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d257082, d258595, d259783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d257091 q = 1) (hb : d258604 q = 1) : d259792 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d257091, d258604, d259792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d257091, d258604, d259792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d257092 q = 1) (hb : d258605 q = 1) : d259793 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d257092, d258605, d259793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d257092, d258605, d259793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro64300 (p : Pattern) (ha : d257098 p = 1) (hb : d258611 p = 1) : d259799 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d257085 q = 1) (hb : d258598 q = 1) : d259786 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d257085, d258598, d259786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64297 q ha hb
    | true =>
      simp only [d257085, d258598, d259786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d257086 q = 1) (hb : d258599 q = 1) : d259787 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d257086, d258599, d259787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d257086, d258599, d259787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d257093 q = 1) (hb : d258606 q = 1) : d259794 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d257093, d258606, d259794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64299 q ha hb
    | true =>
      simp only [d257093, d258606, d259794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d257094 q = 1) (hb : d258607 q = 1) : d259795 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d257094, d258607, d259795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d257094, d258607, d259795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d257095 q = 1) (hb : d258608 q = 1) : d259796 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d257095, d258608, d259796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d257095, d258608, d259796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d257096 q = 1) (hb : d258609 q = 1) : d259797 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d257096, d258609, d259797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d257096, d258609, d259797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d257097 q = 1) (hb : d258610 q = 1) : d259798 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d257097, d258610, d259798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d257097, d258610, d259798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d257098 q = 1) (hb : d258611 q = 1) : d259799 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d257098, d258611, d259799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d257098, d258611, d259799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro64301 (p : Pattern) (ha : d257109 p = 1) (hb : d258617 p = 1) : d259805 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d257085 q = 1) (hb : d258598 q = 1) : d259786 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d257085, d258598, d259786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64297 q ha hb
    | true =>
      simp only [d257085, d258598, d259786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d257086 q = 1) (hb : d258599 q = 1) : d259787 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d257086, d258599, d259787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d257086, d258599, d259787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d257106 q = 1) (hb : d258614 q = 1) : d259802 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d257106, d258614, d259802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d257106, d258614, d259802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d257107 q = 1) (hb : d258615 q = 1) : d259803 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d257107, d258615, d259803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d257107, d258615, d259803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d257108 q = 1) (hb : d258616 q = 1) : d259804 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d257108, d258616, d259804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d257108, d258616, d259804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d257109 q = 1) (hb : d258617 q = 1) : d259805 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d257109, d258617, d259805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d257109, d258617, d259805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro64302 (p : Pattern) (ha : d257115 p = 1) (hb : d258623 p = 1) : d259811 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d257099 q = 1) (hb : d258612 q = 1) : d259800 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d257099, d258612, d259800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64298 q ha hb
    | true =>
      simp only [d257099, d258612, d259800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64300 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d257104 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d257105 q = 1) (hb : d258613 q = 1) : d259801 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d257105, d258613, d259801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d257105, d258613, d259801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d257110 q = 1) (hb : d258618 q = 1) : d259806 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d257110, d258618, d259806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64301 q ha hb
    | true =>
      simp only [d257110, d258618, d259806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d257111 q = 1) (hb : d258619 q = 1) : d259807 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d257111, d258619, d259807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d257111, d258619, d259807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d257112 q = 1) (hb : d258620 q = 1) : d259808 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d257112, d258620, d259808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d257112, d258620, d259808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d257113 q = 1) (hb : d258621 q = 1) : d259809 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d257113, d258621, d259809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d257113, d258621, d259809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d257114 q = 1) (hb : d258622 q = 1) : d259810 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d257114, d258622, d259810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d257114, d258622, d259810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d257115 q = 1) (hb : d258623 q = 1) : d259811 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d257115, d258623, d259811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d257115, d258623, d259811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro64303 (p : Pattern) (ha : d257103 p = 1) (hb : d258628 p = 1) : d259816 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d257093 q = 1) (hb : d258606 q = 1) : d259794 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d257093, d258606, d259794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64299 q ha hb
    | true =>
      simp only [d257093, d258606, d259794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d257094 q = 1) (hb : d258607 q = 1) : d259795 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d257094, d258607, d259795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d257094, d258607, d259795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d257100 q = 1) (hb : d258625 q = 1) : d259813 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d257100, d258625, d259813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d257100, d258625, d259813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d257101 q = 1) (hb : d258626 q = 1) : d259814 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d257101, d258626, d259814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d257101, d258626, d259814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d257102 q = 1) (hb : d258627 q = 1) : d259815 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d257102, d258627, d259815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d257102, d258627, d259815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d257103 q = 1) (hb : d258628 q = 1) : d259816 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d257103, d258628, d259816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d257103, d258628, d259816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro64304 (p : Pattern) (ha : d257122 p = 1) (hb : d258634 p = 1) : d259822 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d257117 q = 1) (hb : d258629 q = 1) : d259817 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d257117, d258629, d259817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64303 q ha hb
    | true =>
      simp only [d257117, d258629, d259817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d257118 q = 1) (hb : d258630 q = 1) : d259818 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d257118, d258630, d259818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d257118, d258630, d259818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d257119 q = 1) (hb : d258631 q = 1) : d259819 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d257119, d258631, d259819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d257119, d258631, d259819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d257120 q = 1) (hb : d258632 q = 1) : d259820 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d257120, d258632, d259820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d257120, d258632, d259820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d257121 q = 1) (hb : d258633 q = 1) : d259821 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d257121, d258633, d259821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d257121, d258633, d259821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d257122 q = 1) (hb : d258634 q = 1) : d259822 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d257122, d258634, d259822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d257122, d258634, d259822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro64305 (p : Pattern) (ha : d257128 p = 1) (hb : d258640 p = 1) : d259828 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d256949 q = 1) (hb : d258446 q = 1) : d259636 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d256949, d258446, d259636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d256949, d258446, d259636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64266 q ha hb
  have h2 (q : Pattern) (ha : d256950 q = 1) (hb : d258447 q = 1) : d259637 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d256950, d258447, d259637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d256950, d258447, d259637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d256959 q = 1) (hb : d258456 q = 1) : d259646 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d256959, d258456, d259646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64266 q ha hb
    | true =>
      simp only [d256959, d258456, d259646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64269 q ha hb
  have h4 (q : Pattern) (ha : d256960 q = 1) (hb : d258457 q = 1) : d259647 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d256960, d258457, d259647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d256960, d258457, d259647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d256961 q = 1) (hb : d258458 q = 1) : d259648 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d256961, d258458, d259648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d256961, d258458, d259648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d257025 q = 1) (hb : d258527 q = 1) : d259716 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d257025, d258527, d259716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64279 q ha hb
    | true =>
      simp only [d257025, d258527, d259716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64286 q ha hb
  have h7 (q : Pattern) (ha : d257038 q = 1) (hb : d258540 q = 1) : d259729 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d257038, d258540, d259729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64287 q ha hb
    | true =>
      simp only [d257038, d258540, d259729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64288 q ha hb
  have h8 (q : Pattern) (ha : d257039 q = 1) (hb : d258541 q = 1) : d259730 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d257039, d258541, d259730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d257039, d258541, d259730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d257040 q = 1) (hb : d258542 q = 1) : d259731 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d257040, d258542, d259731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d257040, d258542, d259731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d257041 q = 1) (hb : d258543 q = 1) : d259732 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d257041, d258543, d259732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d257041, d258543, d259732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d257045 q = 1) (hb : d258547 q = 1) : d259736 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d257045, d258547, d259736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d257045, d258547, d259736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64289 q ha hb
  have h12 (q : Pattern) (ha : d257047 q = 1) (hb : d258549 q = 1) : d259738 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d257047, d258549, d259738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d257047, d258549, d259738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64290 q ha hb
  have h13 (q : Pattern) (ha : d257048 q = 1) (hb : d258550 q = 1) : d259739 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d257048, d258550, d259739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d257048, d258550, d259739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d257049 q = 1) (hb : d258551 q = 1) : d259740 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d257049, d258551, d259740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d257049, d258551, d259740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d257050 q = 1) (hb : d258552 q = 1) : d259741 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d257050, d258552, d259741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d257050, d258552, d259741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d257051 q = 1) (hb : d258553 q = 1) : d259742 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d257051, d258553, d259742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d257051, d258553, d259742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d257116 q = 1) (hb : d258624 q = 1) : d259812 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d257116, d258624, d259812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d257116, d258624, d259812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64302 q ha hb
  have h18 (q : Pattern) (ha : d257123 q = 1) (hb : d258635 q = 1) : d259823 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d257123, d258635, d259823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d257123, d258635, d259823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64304 q ha hb
  have h19 (q : Pattern) (ha : d257124 q = 1) (hb : d258636 q = 1) : d259824 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d257124, d258636, d259824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d257124, d258636, d259824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d257125 q = 1) (hb : d258637 q = 1) : d259825 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d257125, d258637, d259825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d257125, d258637, d259825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d257126 q = 1) (hb : d258638 q = 1) : d259826 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d257126, d258638, d259826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d257126, d258638, d259826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d257127 q = 1) (hb : d258639 q = 1) : d259827 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d257127, d258639, d259827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d257127, d258639, d259827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d257128 q = 1) (hb : d258640 q = 1) : d259828 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d257128, d258640, d259828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d257128, d258640, d259828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro64306 (p : Pattern) (ha : d257134 p = 1) (hb : d258646 p = 1) : d259834 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d257129 q = 1) (hb : d258641 q = 1) : d259829 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d257129, d258641, d259829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d257129, d258641, d259829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64305 q ha hb
  have h2 (q : Pattern) (ha : d257130 q = 1) (hb : d258642 q = 1) : d259830 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d257130, d258642, d259830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d257130, d258642, d259830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d257131 q = 1) (hb : d258643 q = 1) : d259831 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d257131, d258643, d259831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d257131, d258643, d259831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d257132 q = 1) (hb : d258644 q = 1) : d259832 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d257132, d258644, d259832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d257132, d258644, d259832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d257133 q = 1) (hb : d258645 q = 1) : d259833 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d257133, d258645, d259833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d257133, d258645, d259833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d257134 q = 1) (hb : d258646 q = 1) : d259834 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d257134, d258646, d259834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d257134, d258646, d259834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro64307 (p : Pattern) (ha : d257140 p = 1) (hb : d258652 p = 1) : d259840 p = 1 := by
  have h0 (q : Pattern) (ha : d255983 q = 1) (hb : d257549 q = 1) : d258905 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d255983, d257549, d258905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64061 q ha hb
    | true =>
      simp only [d255983, d257549, d258905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64089 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d256230 q = 1) (hb : d257779 q = 1) : d259067 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d256230, d257779, d259067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d256230, d257779, d259067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64136 q ha hb
  have h3 (q : Pattern) (ha : d256231 q = 1) (hb : d257780 q = 1) : d259068 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d256231, d257780, d259068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d256231, d257780, d259068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d256565 q = 1) (hb : d258069 q = 1) : d259288 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d256565, d258069, d259288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d256565, d258069, d259288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64193 q ha hb
  have h5 (q : Pattern) (ha : d256566 q = 1) (hb : d258070 q = 1) : d259289 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d256566, d258070, d259289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d256566, d258070, d259289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d256567 q = 1) (hb : d258071 q = 1) : d259290 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d256567, d258071, d259290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d256567, d258071, d259290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d256892 q = 1) (hb : d258379 q = 1) : d259569 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d256892, d258379, d259569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d256892, d258379, d259569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64253 q ha hb
  have h8 (q : Pattern) (ha : d256893 q = 1) (hb : d258380 q = 1) : d259570 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d256893, d258380, d259570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d256893, d258380, d259570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d256894 q = 1) (hb : d258381 q = 1) : d259571 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d256894, d258381, d259571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d256894, d258381, d259571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d256895 q = 1) (hb : d258382 q = 1) : d259572 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d256895, d258382, d259572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d256895, d258382, d259572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d257135 q = 1) (hb : d258647 q = 1) : d259835 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d257135, d258647, d259835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d257135, d258647, d259835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64306 q ha hb
  have h12 (q : Pattern) (ha : d257136 q = 1) (hb : d258648 q = 1) : d259836 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d257136, d258648, d259836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d257136, d258648, d259836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d257137 q = 1) (hb : d258649 q = 1) : d259837 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d257137, d258649, d259837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d257137, d258649, d259837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d257138 q = 1) (hb : d258650 q = 1) : d259838 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d257138, d258650, d259838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d257138, d258650, d259838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d257139 q = 1) (hb : d258651 q = 1) : d259839 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d257139, d258651, d259839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d257139, d258651, d259839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d257140 q = 1) (hb : d258652 q = 1) : d259840 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d257140, d258652, d259840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d257140, d258652, d259840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro64308 (p : Pattern) (ha : d257146 p = 1) (hb : d258658 p = 1) : d259846 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d257141 q = 1) (hb : d258653 q = 1) : d259841 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d257141, d258653, d259841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64307 q ha hb
    | true =>
      simp only [d257141, d258653, d259841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d257142 q = 1) (hb : d258654 q = 1) : d259842 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d257142, d258654, d259842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d257142, d258654, d259842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d257143 q = 1) (hb : d258655 q = 1) : d259843 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d257143, d258655, d259843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d257143, d258655, d259843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d257144 q = 1) (hb : d258656 q = 1) : d259844 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d257144, d258656, d259844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d257144, d258656, d259844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d257145 q = 1) (hb : d258657 q = 1) : d259845 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d257145, d258657, d259845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d257145, d258657, d259845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d257146 q = 1) (hb : d258658 q = 1) : d259846 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d257146, d258658, d259846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d257146, d258658, d259846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro64309 (p : Pattern) (ha : d257152 p = 1) (hb : d258664 p = 1) : d259852 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d257147 q = 1) (hb : d258659 q = 1) : d259847 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d257147, d258659, d259847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64308 q ha hb
    | true =>
      simp only [d257147, d258659, d259847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d257148 q = 1) (hb : d258660 q = 1) : d259848 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d257148, d258660, d259848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d257148, d258660, d259848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d257149 q = 1) (hb : d258661 q = 1) : d259849 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d257149, d258661, d259849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d257149, d258661, d259849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d257150 q = 1) (hb : d258662 q = 1) : d259850 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d257150, d258662, d259850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d257150, d258662, d259850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d257151 q = 1) (hb : d258663 q = 1) : d259851 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d257151, d258663, d259851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d257151, d258663, d259851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d257152 q = 1) (hb : d258664 q = 1) : d259852 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d257152, d258664, d259852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d257152, d258664, d259852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro64310 (p : Pattern) (ha : d257158 p = 1) (hb : d258670 p = 1) : d259858 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d257153 q = 1) (hb : d258665 q = 1) : d259853 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d257153, d258665, d259853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64309 q ha hb
    | true =>
      simp only [d257153, d258665, d259853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d257154 q = 1) (hb : d258666 q = 1) : d259854 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d257154, d258666, d259854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d257154, d258666, d259854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d257155 q = 1) (hb : d258667 q = 1) : d259855 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d257155, d258667, d259855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d257155, d258667, d259855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d257156 q = 1) (hb : d258668 q = 1) : d259856 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d257156, d258668, d259856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d257156, d258668, d259856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d257157 q = 1) (hb : d258669 q = 1) : d259857 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d257157, d258669, d259857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d257157, d258669, d259857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d257158 q = 1) (hb : d258670 q = 1) : d259858 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d257158, d258670, d259858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d257158, d258670, d259858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro64311 (p : Pattern) (ha : d257164 p = 1) (hb : d258676 p = 1) : d259864 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d257159 q = 1) (hb : d258671 q = 1) : d259859 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d257159, d258671, d259859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64310 q ha hb
    | true =>
      simp only [d257159, d258671, d259859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d257160 q = 1) (hb : d258672 q = 1) : d259860 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d257160, d258672, d259860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d257160, d258672, d259860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d257161 q = 1) (hb : d258673 q = 1) : d259861 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d257161, d258673, d259861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d257161, d258673, d259861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d257162 q = 1) (hb : d258674 q = 1) : d259862 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d257162, d258674, d259862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d257162, d258674, d259862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d257163 q = 1) (hb : d258675 q = 1) : d259863 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d257163, d258675, d259863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d257163, d258675, d259863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d257164 q = 1) (hb : d258676 q = 1) : d259864 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d257164, d258676, d259864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d257164, d258676, d259864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro64312 (p : Pattern) (ha : d257170 p = 1) (hb : d258682 p = 1) : d259870 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d257165 q = 1) (hb : d258677 q = 1) : d259865 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d257165, d258677, d259865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64311 q ha hb
    | true =>
      simp only [d257165, d258677, d259865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d257166 q = 1) (hb : d258678 q = 1) : d259866 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d257166, d258678, d259866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d257166, d258678, d259866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d257167 q = 1) (hb : d258679 q = 1) : d259867 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d257167, d258679, d259867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d257167, d258679, d259867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d257168 q = 1) (hb : d258680 q = 1) : d259868 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d257168, d258680, d259868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d257168, d258680, d259868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d257169 q = 1) (hb : d258681 q = 1) : d259869 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d257169, d258681, d259869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d257169, d258681, d259869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d257170 q = 1) (hb : d258682 q = 1) : d259870 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d257170, d258682, d259870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d257170, d258682, d259870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro64313 (p : Pattern) (ha : d257176 p = 1) (hb : d258688 p = 1) : d259876 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d257171 q = 1) (hb : d258683 q = 1) : d259871 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d257171, d258683, d259871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64312 q ha hb
    | true =>
      simp only [d257171, d258683, d259871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d257172 q = 1) (hb : d258684 q = 1) : d259872 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d257172, d258684, d259872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d257172, d258684, d259872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d257173 q = 1) (hb : d258685 q = 1) : d259873 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d257173, d258685, d259873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d257173, d258685, d259873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d257174 q = 1) (hb : d258686 q = 1) : d259874 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d257174, d258686, d259874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d257174, d258686, d259874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d257175 q = 1) (hb : d258687 q = 1) : d259875 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d257175, d258687, d259875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d257175, d258687, d259875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d257176 q = 1) (hb : d258688 q = 1) : d259876 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d257176, d258688, d259876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d257176, d258688, d259876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro64314 (p : Pattern) (ha : d257182 p = 1) (hb : d258694 p = 1) : d259882 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d257177 q = 1) (hb : d258689 q = 1) : d259877 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d257177, d258689, d259877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64313 q ha hb
    | true =>
      simp only [d257177, d258689, d259877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d257178 q = 1) (hb : d258690 q = 1) : d259878 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d257178, d258690, d259878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d257178, d258690, d259878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d257179 q = 1) (hb : d258691 q = 1) : d259879 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d257179, d258691, d259879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d257179, d258691, d259879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d257180 q = 1) (hb : d258692 q = 1) : d259880 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d257180, d258692, d259880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d257180, d258692, d259880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d257181 q = 1) (hb : d258693 q = 1) : d259881 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d257181, d258693, d259881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d257181, d258693, d259881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d257182 q = 1) (hb : d258694 q = 1) : d259882 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d257182, d258694, d259882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d257182, d258694, d259882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro64315 (p : Pattern) (ha : d53647 p = 1) (hb : d253272 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63661 q ha hb
    | true =>
      simp only [d112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63662 q ha hb
  have h2 (q : Pattern) (ha : d113 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53637 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53638 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d407 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63682 q ha hb
  have h6 (q : Pattern) (ha : d53639 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d53640 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d53641 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d53642 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d463 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63683 q ha hb
  have h11 (q : Pattern) (ha : d53643 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d53643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d53644 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d53644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d53645 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d53646 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d53646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d53647 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d53647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro64316 (p : Pattern) (ha : d245682 p = 1) (hb : d253272 p = 1) : d257490 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25130 q = 1) (hb : d253272 q = 1) : d257214 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25130, d257214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63674 q ha hb
    | true =>
      simp only [d25130, d257214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63653 q ha hb
  have h2 (q : Pattern) (ha : d25190 q = 1) (hb : d253272 q = 1) : d257272 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25190, d257272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25190, d257272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25191 q = 1) (hb : d253272 q = 1) : d257273 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25191, d257273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25191, d257273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25192 q = 1) (hb : d253272 q = 1) : d257274 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25192, d257274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25192, d257274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25193 q = 1) (hb : d253272 q = 1) : d257275 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d25193, d257275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25193, d257275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d245682 q = 1) (hb : d253272 q = 1) : d257490 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245682, d257490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245682, d257490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro64317 (p : Pattern) (ha : d245692 p = 1) (hb : d253272 p = 1) : d257536 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25166 q = 1) (hb : d253272 q = 1) : d257248 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25166, d257248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63679 q ha hb
    | true =>
      simp only [d25166, d257248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63658 q ha hb
  have h2 (q : Pattern) (ha : d245688 q = 1) (hb : d253272 q = 1) : d257532 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245688, d257532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245688, d257532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d245689 q = 1) (hb : d253272 q = 1) : d257533 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245689, d257533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d245689, d257533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d245690 q = 1) (hb : d253272 q = 1) : d257534 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245690, d257534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245690, d257534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d245691 q = 1) (hb : d253272 q = 1) : d257535 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245691, d257535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245691, d257535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d245692 q = 1) (hb : d253272 q = 1) : d257536 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245692, d257536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245692, d257536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro64318 (p : Pattern) (ha : d245698 p = 1) (hb : d253272 p = 1) : d259893 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25195 q = 1) (hb : d253272 q = 1) : d257277 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d25195, d257277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63684 q ha hb
    | true =>
      simp only [d25195, d257277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63685 q ha hb
  have h2 (q : Pattern) (ha : d25196 q = 1) (hb : d253272 q = 1) : d257278 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d25196, d257278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d25196, d257278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d245680 q = 1) (hb : d253272 q = 1) : d259883 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245680, d259883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d245680, d259883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d245681 q = 1) (hb : d253272 q = 1) : d259884 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245681, d259884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245681, d259884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d245683 q = 1) (hb : d253272 q = 1) : d257491 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245683, d257491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245683, d257491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64316 q ha hb
  have h6 (q : Pattern) (ha : d245684 q = 1) (hb : d253272 q = 1) : d259885 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245684, d259885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d245684, d259885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d245685 q = 1) (hb : d253272 q = 1) : d259886 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245685, d259886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d245685, d259886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d245686 q = 1) (hb : d253272 q = 1) : d259887 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245686, d259887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d245686, d259887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d245687 q = 1) (hb : d253272 q = 1) : d259888 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d245687, d259888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245687, d259888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d245693 q = 1) (hb : d253272 q = 1) : d257537 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245693, d257537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245693, d257537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64317 q ha hb
  have h11 (q : Pattern) (ha : d245694 q = 1) (hb : d253272 q = 1) : d259889 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245694, d259889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d245694, d259889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d245695 q = 1) (hb : d253272 q = 1) : d259890 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245695, d259890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d245695, d259890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d245696 q = 1) (hb : d253272 q = 1) : d259891 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245696, d259891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d245696, d259891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d245697 q = 1) (hb : d253272 q = 1) : d259892 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d245697, d259892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d245697, d259892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d245698 q = 1) (hb : d253272 q = 1) : d259893 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d245698, d259893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d245698, d259893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro64319 (p : Pattern) (ha : d245704 p = 1) (hb : d253272 p = 1) : d259899 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53648 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64315 q ha hb
  have h2 (q : Pattern) (ha : d53649 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53650 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53651 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53652 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d245699 q = 1) (hb : d253272 q = 1) : d259894 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d245699, d259894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245699, d259894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64318 q ha hb
  have h7 (q : Pattern) (ha : d245700 q = 1) (hb : d253272 q = 1) : d259895 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d245700, d259895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245700, d259895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d245701 q = 1) (hb : d253272 q = 1) : d259896 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d245701, d259896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245701, d259896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d245702 q = 1) (hb : d253272 q = 1) : d259897 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d245702, d259897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245702, d259897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d245703 q = 1) (hb : d253272 q = 1) : d259898 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d245703, d259898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245703, d259898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d245704 q = 1) (hb : d253272 q = 1) : d259899 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d245704, d259899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d245704, d259899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro64320 (p : Pattern) (ha : d245707 p = 1) (hb : d253272 p = 1) : d259902 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25402 q = 1) (hb : d253272 q = 1) : d257333 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25402, d257333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63715 q ha hb
    | true =>
      simp only [d25402, d257333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63716 q ha hb
  have h2 (q : Pattern) (ha : d25403 q = 1) (hb : d253272 q = 1) : d257396 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25403, d257396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25403, d257396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25404 q = 1) (hb : d253272 q = 1) : d257397 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25404, d257397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25404, d257397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25405 q = 1) (hb : d253272 q = 1) : d257398 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25405, d257398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25405, d257398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25406 q = 1) (hb : d253272 q = 1) : d257399 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d25406, d257399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25406, d257399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d245707 q = 1) (hb : d253272 q = 1) : d259902 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245707, d259902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245707, d259902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro64321 (p : Pattern) (ha : d245718 p = 1) (hb : d253272 p = 1) : d259912 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d245713 q = 1) (hb : d253272 q = 1) : d257371 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d245713, d257371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63753 q ha hb
    | true =>
      simp only [d245713, d257371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63722 q ha hb
  have h2 (q : Pattern) (ha : d245714 q = 1) (hb : d253272 q = 1) : d259908 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245714, d259908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245714, d259908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d245715 q = 1) (hb : d253272 q = 1) : d259909 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245715, d259909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d245715, d259909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d245716 q = 1) (hb : d253272 q = 1) : d259910 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245716, d259910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245716, d259910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d245717 q = 1) (hb : d253272 q = 1) : d259911 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245717, d259911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245717, d259911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d245718 q = 1) (hb : d253272 q = 1) : d259912 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245718, d259912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245718, d259912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro64322 (p : Pattern) (ha : d245724 p = 1) (hb : d253272 p = 1) : d259918 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25408 q = 1) (hb : d253272 q = 1) : d257401 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d25408, d257401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63714 q ha hb
    | true =>
      simp only [d25408, d257401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63717 q ha hb
  have h2 (q : Pattern) (ha : d25409 q = 1) (hb : d253272 q = 1) : d257402 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d25409, d257402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d25409, d257402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d245705 q = 1) (hb : d253272 q = 1) : d259900 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245705, d259900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d245705, d259900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d245706 q = 1) (hb : d253272 q = 1) : d259901 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245706, d259901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245706, d259901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d245708 q = 1) (hb : d253272 q = 1) : d259903 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245708, d259903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245708, d259903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64320 q ha hb
  have h6 (q : Pattern) (ha : d245709 q = 1) (hb : d253272 q = 1) : d259904 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245709, d259904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d245709, d259904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d245710 q = 1) (hb : d253272 q = 1) : d259905 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245710, d259905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d245710, d259905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d245711 q = 1) (hb : d253272 q = 1) : d259906 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245711, d259906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d245711, d259906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d245712 q = 1) (hb : d253272 q = 1) : d259907 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d245712, d259907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245712, d259907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d245719 q = 1) (hb : d253272 q = 1) : d259913 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245719, d259913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245719, d259913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64321 q ha hb
  have h11 (q : Pattern) (ha : d245720 q = 1) (hb : d253272 q = 1) : d259914 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245720, d259914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d245720, d259914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d245721 q = 1) (hb : d253272 q = 1) : d259915 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245721, d259915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d245721, d259915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d245722 q = 1) (hb : d253272 q = 1) : d259916 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245722, d259916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d245722, d259916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d245723 q = 1) (hb : d253272 q = 1) : d259917 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d245723, d259917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d245723, d259917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d245724 q = 1) (hb : d253272 q = 1) : d259918 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d245724, d259918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d245724, d259918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro64323 (p : Pattern) (ha : d245730 p = 1) (hb : d253272 p = 1) : d259924 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d245725 q = 1) (hb : d253272 q = 1) : d259919 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d245725, d259919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245725, d259919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64322 q ha hb
  have h2 (q : Pattern) (ha : d245726 q = 1) (hb : d253272 q = 1) : d259920 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d245726, d259920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245726, d259920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d245727 q = 1) (hb : d253272 q = 1) : d259921 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d245727, d259921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245727, d259921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d245728 q = 1) (hb : d253272 q = 1) : d259922 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d245728, d259922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245728, d259922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d245729 q = 1) (hb : d253272 q = 1) : d259923 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d245729, d259923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245729, d259923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d245730 q = 1) (hb : d253272 q = 1) : d259924 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d245730, d259924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245730, d259924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro64324 (p : Pattern) (ha : d245734 p = 1) (hb : d253272 p = 1) : d259928 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25735 q = 1) (hb : d253272 q = 1) : d257577 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25735, d257577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63767 q ha hb
    | true =>
      simp only [d25735, d257577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63768 q ha hb
  have h2 (q : Pattern) (ha : d25736 q = 1) (hb : d253272 q = 1) : d257578 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25736, d257578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25736, d257578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25737 q = 1) (hb : d253272 q = 1) : d257579 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25737, d257579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25737, d257579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25738 q = 1) (hb : d253272 q = 1) : d257580 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25738, d257580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25738, d257580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25739 q = 1) (hb : d253272 q = 1) : d257581 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d25739, d257581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25739, d257581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d245734 q = 1) (hb : d253272 q = 1) : d259928 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245734, d259928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245734, d259928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro64325 (p : Pattern) (ha : d245745 p = 1) (hb : d253272 p = 1) : d259939 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d245740 q = 1) (hb : d253272 q = 1) : d259934 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d245740, d259934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63808 q ha hb
    | true =>
      simp only [d245740, d259934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63776 q ha hb
  have h2 (q : Pattern) (ha : d245741 q = 1) (hb : d253272 q = 1) : d259935 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245741, d259935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245741, d259935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d245742 q = 1) (hb : d253272 q = 1) : d259936 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245742, d259936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d245742, d259936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d245743 q = 1) (hb : d253272 q = 1) : d259937 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245743, d259937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245743, d259937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d245744 q = 1) (hb : d253272 q = 1) : d259938 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245744, d259938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245744, d259938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d245745 q = 1) (hb : d253272 q = 1) : d259939 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245745, d259939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245745, d259939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro64326 (p : Pattern) (ha : d245751 p = 1) (hb : d253272 p = 1) : d259945 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25741 q = 1) (hb : d253272 q = 1) : d257583 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d25741, d257583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63766 q ha hb
    | true =>
      simp only [d25741, d257583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63769 q ha hb
  have h2 (q : Pattern) (ha : d25742 q = 1) (hb : d253272 q = 1) : d257584 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d25742, d257584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d25742, d257584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d245732 q = 1) (hb : d253272 q = 1) : d259926 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245732, d259926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d245732, d259926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d245733 q = 1) (hb : d253272 q = 1) : d259927 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245733, d259927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245733, d259927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d245735 q = 1) (hb : d253272 q = 1) : d259929 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245735, d259929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245735, d259929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64324 q ha hb
  have h6 (q : Pattern) (ha : d245736 q = 1) (hb : d253272 q = 1) : d259930 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245736, d259930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d245736, d259930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d245737 q = 1) (hb : d253272 q = 1) : d259931 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245737, d259931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d245737, d259931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d245738 q = 1) (hb : d253272 q = 1) : d259932 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245738, d259932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d245738, d259932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d245739 q = 1) (hb : d253272 q = 1) : d259933 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d245739, d259933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245739, d259933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d245746 q = 1) (hb : d253272 q = 1) : d259940 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245746, d259940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245746, d259940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64325 q ha hb
  have h11 (q : Pattern) (ha : d245747 q = 1) (hb : d253272 q = 1) : d259941 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245747, d259941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d245747, d259941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d245748 q = 1) (hb : d253272 q = 1) : d259942 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245748, d259942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d245748, d259942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d245749 q = 1) (hb : d253272 q = 1) : d259943 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245749, d259943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d245749, d259943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d245750 q = 1) (hb : d253272 q = 1) : d259944 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d245750, d259944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d245750, d259944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d245751 q = 1) (hb : d253272 q = 1) : d259945 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d245751, d259945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d245751, d259945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro64327 (p : Pattern) (ha : d245757 p = 1) (hb : d253272 p = 1) : d259951 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d245752 q = 1) (hb : d253272 q = 1) : d259946 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d245752, d259946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245752, d259946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64326 q ha hb
  have h2 (q : Pattern) (ha : d245753 q = 1) (hb : d253272 q = 1) : d259947 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d245753, d259947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245753, d259947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d245754 q = 1) (hb : d253272 q = 1) : d259948 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d245754, d259948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245754, d259948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d245755 q = 1) (hb : d253272 q = 1) : d259949 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d245755, d259949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245755, d259949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d245756 q = 1) (hb : d253272 q = 1) : d259950 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d245756, d259950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245756, d259950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d245757 q = 1) (hb : d253272 q = 1) : d259951 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d245757, d259951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245757, d259951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro64328 (p : Pattern) (ha : d245762 p = 1) (hb : d253272 p = 1) : d259956 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26159 q = 1) (hb : d253272 q = 1) : d257844 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d26159, d257844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63829 q ha hb
    | true =>
      simp only [d26159, d257844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63830 q ha hb
  have h2 (q : Pattern) (ha : d26160 q = 1) (hb : d253272 q = 1) : d257845 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d26160, d257845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26160, d257845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d26161 q = 1) (hb : d253272 q = 1) : d257846 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d26161, d257846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26161, d257846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d26162 q = 1) (hb : d253272 q = 1) : d257847 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d26162, d257847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26162, d257847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d26163 q = 1) (hb : d253272 q = 1) : d257848 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d26163, d257848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26163, d257848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d245762 q = 1) (hb : d253272 q = 1) : d259956 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245762, d259956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245762, d259956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro64329 (p : Pattern) (ha : d245773 p = 1) (hb : d253272 p = 1) : d259967 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d245768 q = 1) (hb : d253272 q = 1) : d259962 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d245768, d259962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63871 q ha hb
    | true =>
      simp only [d245768, d259962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63838 q ha hb
  have h2 (q : Pattern) (ha : d245769 q = 1) (hb : d253272 q = 1) : d259963 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245769, d259963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245769, d259963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d245770 q = 1) (hb : d253272 q = 1) : d259964 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245770, d259964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d245770, d259964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d245771 q = 1) (hb : d253272 q = 1) : d259965 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245771, d259965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245771, d259965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d245772 q = 1) (hb : d253272 q = 1) : d259966 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245772, d259966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245772, d259966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d245773 q = 1) (hb : d253272 q = 1) : d259967 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245773, d259967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245773, d259967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro64330 (p : Pattern) (ha : d245779 p = 1) (hb : d253272 p = 1) : d259973 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26165 q = 1) (hb : d253272 q = 1) : d257850 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d26165, d257850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63828 q ha hb
    | true =>
      simp only [d26165, d257850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63831 q ha hb
  have h2 (q : Pattern) (ha : d26166 q = 1) (hb : d253272 q = 1) : d257851 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d26166, d257851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d26166, d257851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d245760 q = 1) (hb : d253272 q = 1) : d259954 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245760, d259954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d245760, d259954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d245761 q = 1) (hb : d253272 q = 1) : d259955 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245761, d259955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245761, d259955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d245763 q = 1) (hb : d253272 q = 1) : d259957 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245763, d259957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245763, d259957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64328 q ha hb
  have h6 (q : Pattern) (ha : d245764 q = 1) (hb : d253272 q = 1) : d259958 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245764, d259958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d245764, d259958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d245765 q = 1) (hb : d253272 q = 1) : d259959 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245765, d259959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d245765, d259959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d245766 q = 1) (hb : d253272 q = 1) : d259960 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245766, d259960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d245766, d259960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d245767 q = 1) (hb : d253272 q = 1) : d259961 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d245767, d259961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245767, d259961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d245774 q = 1) (hb : d253272 q = 1) : d259968 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245774, d259968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245774, d259968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64329 q ha hb
  have h11 (q : Pattern) (ha : d245775 q = 1) (hb : d253272 q = 1) : d259969 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245775, d259969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d245775, d259969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d245776 q = 1) (hb : d253272 q = 1) : d259970 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245776, d259970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d245776, d259970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d245777 q = 1) (hb : d253272 q = 1) : d259971 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245777, d259971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d245777, d259971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d245778 q = 1) (hb : d253272 q = 1) : d259972 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d245778, d259972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d245778, d259972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d245779 q = 1) (hb : d253272 q = 1) : d259973 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d245779, d259973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d245779, d259973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro64331 (p : Pattern) (ha : d245785 p = 1) (hb : d253272 p = 1) : d259979 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d245780 q = 1) (hb : d253272 q = 1) : d259974 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d245780, d259974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245780, d259974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64330 q ha hb
  have h2 (q : Pattern) (ha : d245781 q = 1) (hb : d253272 q = 1) : d259975 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d245781, d259975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245781, d259975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d245782 q = 1) (hb : d253272 q = 1) : d259976 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d245782, d259976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245782, d259976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d245783 q = 1) (hb : d253272 q = 1) : d259977 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d245783, d259977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245783, d259977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d245784 q = 1) (hb : d253272 q = 1) : d259978 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d245784, d259978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245784, d259978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d245785 q = 1) (hb : d253272 q = 1) : d259979 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d245785, d259979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245785, d259979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro64332 (p : Pattern) (ha : d245791 p = 1) (hb : d253272 p = 1) : d259985 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26626 q = 1) (hb : d253272 q = 1) : d258157 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d26626, d258157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63899 q ha hb
    | true =>
      simp only [d26626, d258157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63900 q ha hb
  have h2 (q : Pattern) (ha : d26627 q = 1) (hb : d253272 q = 1) : d258158 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d26627, d258158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26627, d258158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d26628 q = 1) (hb : d253272 q = 1) : d258159 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d26628, d258159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26628, d258159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d26629 q = 1) (hb : d253272 q = 1) : d258160 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d26629, d258160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26629, d258160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d26630 q = 1) (hb : d253272 q = 1) : d258161 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d26630, d258161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26630, d258161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d245791 q = 1) (hb : d253272 q = 1) : d259985 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245791, d259985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245791, d259985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro64333 (p : Pattern) (ha : d245802 p = 1) (hb : d253272 p = 1) : d259996 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d245797 q = 1) (hb : d253272 q = 1) : d259991 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d245797, d259991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63941 q ha hb
    | true =>
      simp only [d245797, d259991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63908 q ha hb
  have h2 (q : Pattern) (ha : d245798 q = 1) (hb : d253272 q = 1) : d259992 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245798, d259992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245798, d259992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d245799 q = 1) (hb : d253272 q = 1) : d259993 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245799, d259993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d245799, d259993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d245800 q = 1) (hb : d253272 q = 1) : d259994 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245800, d259994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245800, d259994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d245801 q = 1) (hb : d253272 q = 1) : d259995 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245801, d259995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245801, d259995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d245802 q = 1) (hb : d253272 q = 1) : d259996 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245802, d259996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245802, d259996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro64334 (p : Pattern) (ha : d245808 p = 1) (hb : d253272 p = 1) : d260002 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26632 q = 1) (hb : d253272 q = 1) : d258163 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d26632, d258163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63898 q ha hb
    | true =>
      simp only [d26632, d258163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63901 q ha hb
  have h2 (q : Pattern) (ha : d26633 q = 1) (hb : d253272 q = 1) : d258164 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d26633, d258164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d26633, d258164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d245789 q = 1) (hb : d253272 q = 1) : d259983 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245789, d259983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d245789, d259983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d245790 q = 1) (hb : d253272 q = 1) : d259984 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245790, d259984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245790, d259984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d245792 q = 1) (hb : d253272 q = 1) : d259986 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245792, d259986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245792, d259986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64332 q ha hb
  have h6 (q : Pattern) (ha : d245793 q = 1) (hb : d253272 q = 1) : d259987 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245793, d259987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d245793, d259987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d245794 q = 1) (hb : d253272 q = 1) : d259988 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245794, d259988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d245794, d259988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d245795 q = 1) (hb : d253272 q = 1) : d259989 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245795, d259989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d245795, d259989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d245796 q = 1) (hb : d253272 q = 1) : d259990 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d245796, d259990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245796, d259990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d245803 q = 1) (hb : d253272 q = 1) : d259997 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245803, d259997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245803, d259997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64333 q ha hb
  have h11 (q : Pattern) (ha : d245804 q = 1) (hb : d253272 q = 1) : d259998 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245804, d259998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d245804, d259998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d245805 q = 1) (hb : d253272 q = 1) : d259999 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245805, d259999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d245805, d259999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d245806 q = 1) (hb : d253272 q = 1) : d260000 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245806, d260000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d245806, d260000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d245807 q = 1) (hb : d253272 q = 1) : d260001 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d245807, d260001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d245807, d260001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d245808 q = 1) (hb : d253272 q = 1) : d260002 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d245808, d260002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d245808, d260002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro64335 (p : Pattern) (ha : d245814 p = 1) (hb : d253272 p = 1) : d260008 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d245809 q = 1) (hb : d253272 q = 1) : d260003 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d245809, d260003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245809, d260003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64334 q ha hb
  have h2 (q : Pattern) (ha : d245810 q = 1) (hb : d253272 q = 1) : d260004 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d245810, d260004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245810, d260004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d245811 q = 1) (hb : d253272 q = 1) : d260005 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d245811, d260005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245811, d260005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d245812 q = 1) (hb : d253272 q = 1) : d260006 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d245812, d260006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245812, d260006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d245813 q = 1) (hb : d253272 q = 1) : d260007 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d245813, d260007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245813, d260007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d245814 q = 1) (hb : d253272 q = 1) : d260008 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d245814, d260008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245814, d260008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro64336 (p : Pattern) (ha : d245821 p = 1) (hb : d253272 p = 1) : d260015 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d27079 q = 1) (hb : d253272 q = 1) : d258450 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d27079, d258450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63969 q ha hb
    | true =>
      simp only [d27079, d258450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63970 q ha hb
  have h2 (q : Pattern) (ha : d27080 q = 1) (hb : d253272 q = 1) : d258451 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d27080, d258451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27080, d258451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d27081 q = 1) (hb : d253272 q = 1) : d258452 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d27081, d258452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d27081, d258452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d27082 q = 1) (hb : d253272 q = 1) : d258453 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d27082, d258453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27082, d258453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d27083 q = 1) (hb : d253272 q = 1) : d258454 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d27083, d258454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27083, d258454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d245821 q = 1) (hb : d253272 q = 1) : d260015 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245821, d260015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245821, d260015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro64337 (p : Pattern) (ha : d245832 p = 1) (hb : d253272 p = 1) : d260026 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d245827 q = 1) (hb : d253272 q = 1) : d260021 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d245827, d260021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64010 q ha hb
    | true =>
      simp only [d245827, d260021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63978 q ha hb
  have h2 (q : Pattern) (ha : d245828 q = 1) (hb : d253272 q = 1) : d260022 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245828, d260022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245828, d260022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d245829 q = 1) (hb : d253272 q = 1) : d260023 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245829, d260023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d245829, d260023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d245830 q = 1) (hb : d253272 q = 1) : d260024 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245830, d260024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245830, d260024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d245831 q = 1) (hb : d253272 q = 1) : d260025 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245831, d260025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245831, d260025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d245832 q = 1) (hb : d253272 q = 1) : d260026 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245832, d260026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245832, d260026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro64338 (p : Pattern) (ha : d245838 p = 1) (hb : d253272 p = 1) : d260032 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d27085 q = 1) (hb : d253272 q = 1) : d258456 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d27085, d258456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63968 q ha hb
    | true =>
      simp only [d27085, d258456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63971 q ha hb
  have h2 (q : Pattern) (ha : d27086 q = 1) (hb : d253272 q = 1) : d258457 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d27086, d258457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d27086, d258457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d245819 q = 1) (hb : d253272 q = 1) : d260013 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245819, d260013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d245819, d260013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d245820 q = 1) (hb : d253272 q = 1) : d260014 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245820, d260014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245820, d260014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d245822 q = 1) (hb : d253272 q = 1) : d260016 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245822, d260016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245822, d260016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64336 q ha hb
  have h6 (q : Pattern) (ha : d245823 q = 1) (hb : d253272 q = 1) : d260017 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245823, d260017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d245823, d260017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d245824 q = 1) (hb : d253272 q = 1) : d260018 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245824, d260018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d245824, d260018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d245825 q = 1) (hb : d253272 q = 1) : d260019 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245825, d260019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d245825, d260019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d245826 q = 1) (hb : d253272 q = 1) : d260020 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d245826, d260020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245826, d260020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d245833 q = 1) (hb : d253272 q = 1) : d260027 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245833, d260027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245833, d260027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64337 q ha hb
  have h11 (q : Pattern) (ha : d245834 q = 1) (hb : d253272 q = 1) : d260028 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245834, d260028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d245834, d260028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d245835 q = 1) (hb : d253272 q = 1) : d260029 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245835, d260029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d245835, d260029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d245836 q = 1) (hb : d253272 q = 1) : d260030 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245836, d260030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d245836, d260030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d245837 q = 1) (hb : d253272 q = 1) : d260031 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d245837, d260031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d245837, d260031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d245838 q = 1) (hb : d253272 q = 1) : d260032 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d245838, d260032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d245838, d260032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro64339 (p : Pattern) (ha : d245844 p = 1) (hb : d253272 p = 1) : d260038 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d245839 q = 1) (hb : d253272 q = 1) : d260033 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d245839, d260033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245839, d260033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64338 q ha hb
  have h2 (q : Pattern) (ha : d245840 q = 1) (hb : d253272 q = 1) : d260034 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d245840, d260034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245840, d260034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d245841 q = 1) (hb : d253272 q = 1) : d260035 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d245841, d260035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245841, d260035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d245842 q = 1) (hb : d253272 q = 1) : d260036 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d245842, d260036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245842, d260036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d245843 q = 1) (hb : d253272 q = 1) : d260037 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d245843, d260037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245843, d260037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d245844 q = 1) (hb : d253272 q = 1) : d260038 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d245844, d260038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245844, d260038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro64340 (p : Pattern) (ha : d245850 p = 1) (hb : d253272 p = 1) : d260044 p = 1 := by
  have h0 (q : Pattern) (ha : d245731 q = 1) (hb : d253272 q = 1) : d259925 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d245731, d259925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64319 q ha hb
    | true =>
      simp only [d245731, d259925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64323 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d245758 q = 1) (hb : d253272 q = 1) : d259952 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d245758, d259952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245758, d259952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64327 q ha hb
  have h3 (q : Pattern) (ha : d245759 q = 1) (hb : d253272 q = 1) : d259953 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d245759, d259953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245759, d259953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d245786 q = 1) (hb : d253272 q = 1) : d259980 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d245786, d259980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245786, d259980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64331 q ha hb
  have h5 (q : Pattern) (ha : d245787 q = 1) (hb : d253272 q = 1) : d259981 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d245787, d259981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245787, d259981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d245788 q = 1) (hb : d253272 q = 1) : d259982 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d245788, d259982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245788, d259982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d245815 q = 1) (hb : d253272 q = 1) : d260009 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d245815, d260009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245815, d260009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64335 q ha hb
  have h8 (q : Pattern) (ha : d245816 q = 1) (hb : d253272 q = 1) : d260010 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d245816, d260010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245816, d260010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d245817 q = 1) (hb : d253272 q = 1) : d260011 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d245817, d260011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245817, d260011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d245818 q = 1) (hb : d253272 q = 1) : d260012 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d245818, d260012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d245818, d260012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d245845 q = 1) (hb : d253272 q = 1) : d260039 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d245845, d260039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245845, d260039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64339 q ha hb
  have h12 (q : Pattern) (ha : d245846 q = 1) (hb : d253272 q = 1) : d260040 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d245846, d260040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245846, d260040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d245847 q = 1) (hb : d253272 q = 1) : d260041 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d245847, d260041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245847, d260041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d245848 q = 1) (hb : d253272 q = 1) : d260042 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d245848, d260042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245848, d260042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d245849 q = 1) (hb : d253272 q = 1) : d260043 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d245849, d260043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d245849, d260043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d245850 q = 1) (hb : d253272 q = 1) : d260044 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d245850, d260044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d245850, d260044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro64341 (p : Pattern) (ha : d245856 p = 1) (hb : d253272 p = 1) : d260050 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d245851 q = 1) (hb : d253272 q = 1) : d260045 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d245851, d260045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64340 q ha hb
    | true =>
      simp only [d245851, d260045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d245852 q = 1) (hb : d253272 q = 1) : d260046 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d245852, d260046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245852, d260046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d245853 q = 1) (hb : d253272 q = 1) : d260047 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d245853, d260047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d245853, d260047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d245854 q = 1) (hb : d253272 q = 1) : d260048 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d245854, d260048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245854, d260048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d245855 q = 1) (hb : d253272 q = 1) : d260049 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d245855, d260049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245855, d260049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d245856 q = 1) (hb : d253272 q = 1) : d260050 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d245856, d260050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d245856, d260050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro64342 (p : Pattern) (ha : d245862 p = 1) (hb : d253272 p = 1) : d260056 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d245857 q = 1) (hb : d253272 q = 1) : d260051 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d245857, d260051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64341 q ha hb
    | true =>
      simp only [d245857, d260051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d245858 q = 1) (hb : d253272 q = 1) : d260052 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d245858, d260052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245858, d260052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d245859 q = 1) (hb : d253272 q = 1) : d260053 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d245859, d260053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d245859, d260053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d245860 q = 1) (hb : d253272 q = 1) : d260054 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d245860, d260054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245860, d260054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d245861 q = 1) (hb : d253272 q = 1) : d260055 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d245861, d260055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245861, d260055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d245862 q = 1) (hb : d253272 q = 1) : d260056 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d245862, d260056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d245862, d260056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro64343 (p : Pattern) (ha : d245868 p = 1) (hb : d253272 p = 1) : d260062 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d245863 q = 1) (hb : d253272 q = 1) : d260057 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d245863, d260057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64342 q ha hb
    | true =>
      simp only [d245863, d260057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d245864 q = 1) (hb : d253272 q = 1) : d260058 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d245864, d260058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245864, d260058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d245865 q = 1) (hb : d253272 q = 1) : d260059 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d245865, d260059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d245865, d260059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d245866 q = 1) (hb : d253272 q = 1) : d260060 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d245866, d260060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245866, d260060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d245867 q = 1) (hb : d253272 q = 1) : d260061 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d245867, d260061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245867, d260061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d245868 q = 1) (hb : d253272 q = 1) : d260062 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d245868, d260062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d245868, d260062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro64344 (p : Pattern) (ha : d245874 p = 1) (hb : d253272 p = 1) : d260068 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d245869 q = 1) (hb : d253272 q = 1) : d260063 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d245869, d260063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64343 q ha hb
    | true =>
      simp only [d245869, d260063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d245870 q = 1) (hb : d253272 q = 1) : d260064 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d245870, d260064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245870, d260064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d245871 q = 1) (hb : d253272 q = 1) : d260065 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d245871, d260065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d245871, d260065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d245872 q = 1) (hb : d253272 q = 1) : d260066 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d245872, d260066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245872, d260066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d245873 q = 1) (hb : d253272 q = 1) : d260067 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d245873, d260067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245873, d260067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d245874 q = 1) (hb : d253272 q = 1) : d260068 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d245874, d260068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d245874, d260068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro64345 (p : Pattern) (ha : d245880 p = 1) (hb : d253272 p = 1) : d260074 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d245875 q = 1) (hb : d253272 q = 1) : d260069 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d245875, d260069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64344 q ha hb
    | true =>
      simp only [d245875, d260069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d245876 q = 1) (hb : d253272 q = 1) : d260070 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d245876, d260070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245876, d260070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d245877 q = 1) (hb : d253272 q = 1) : d260071 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d245877, d260071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d245877, d260071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d245878 q = 1) (hb : d253272 q = 1) : d260072 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d245878, d260072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245878, d260072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d245879 q = 1) (hb : d253272 q = 1) : d260073 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d245879, d260073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245879, d260073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d245880 q = 1) (hb : d253272 q = 1) : d260074 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d245880, d260074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d245880, d260074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro64346 (p : Pattern) (ha : d245886 p = 1) (hb : d253272 p = 1) : d260080 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d245881 q = 1) (hb : d253272 q = 1) : d260075 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d245881, d260075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64345 q ha hb
    | true =>
      simp only [d245881, d260075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d245882 q = 1) (hb : d253272 q = 1) : d260076 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d245882, d260076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245882, d260076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d245883 q = 1) (hb : d253272 q = 1) : d260077 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d245883, d260077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d245883, d260077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d245884 q = 1) (hb : d253272 q = 1) : d260078 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d245884, d260078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245884, d260078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d245885 q = 1) (hb : d253272 q = 1) : d260079 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d245885, d260079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245885, d260079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d245886 q = 1) (hb : d253272 q = 1) : d260080 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d245886, d260080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d245886, d260080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro64347 (p : Pattern) (ha : d245892 p = 1) (hb : d253272 p = 1) : d260086 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d253272 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d245887 q = 1) (hb : d253272 q = 1) : d260081 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d245887, d260081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64346 q ha hb
    | true =>
      simp only [d245887, d260081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d245888 q = 1) (hb : d253272 q = 1) : d260082 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d245888, d260082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245888, d260082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d245889 q = 1) (hb : d253272 q = 1) : d260083 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d245889, d260083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d245889, d260083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d245890 q = 1) (hb : d253272 q = 1) : d260084 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d245890, d260084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245890, d260084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d245891 q = 1) (hb : d253272 q = 1) : d260085 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d245891, d260085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245891, d260085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d245892 q = 1) (hb : d253272 q = 1) : d260086 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d245892, d260086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d245892, d260086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro64348 (p : Pattern) (ha : d255755 p = 1) (hb : d257269 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d255717 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d255723 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d255750 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d255639 q = 1) (hb : d257207 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d255639, d257207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64030 q ha hb
    | true =>
      simp only [d255639, d257207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d255751 q = 1) (hb : d257265 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d255751, d257265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d255751, d257265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d255640 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d255752 q = 1) (hb : d257266 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d255752, d257266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d255752, d257266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d255753 q = 1) (hb : d257267 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d255753, d257267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d255753, d257267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d255754 q = 1) (hb : d257268 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d255754, d257268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d255754, d257268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d255755 q = 1) (hb : d257269 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d255755, d257269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d255755, d257269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro64349 (p : Pattern) (ha : d255771 p = 1) (hb : d257276 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d255717 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d255723 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d255750 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d255639 q = 1) (hb : d257207 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d255639, d257207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64030 q ha hb
    | true =>
      simp only [d255639, d257207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d255751 q = 1) (hb : d257265 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d255751, d257265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d255751, d257265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d255640 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d255752 q = 1) (hb : d257266 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d255752, d257266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d255752, d257266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d255753 q = 1) (hb : d257267 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d255753, d257267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d255753, d257267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d255754 q = 1) (hb : d257268 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d255754, d257268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d255754, d257268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d255760 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d255764 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d255766 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d255646 q = 1) (hb : d257214 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d255646, d257214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64032 q ha hb
    | true =>
      simp only [d255646, d257214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h14 (q : Pattern) (ha : d255767 q = 1) (hb : d257272 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d255767, d257272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
    | true =>
      simp only [d255767, d257272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d255647 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d255768 q = 1) (hb : d257273 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d255768, d257273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d255768, d257273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
  have h17 (q : Pattern) (ha : d255769 q = 1) (hb : d257274 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d255769, d257274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d255769, d257274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d255770 q = 1) (hb : d257275 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d255770, d257275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d255770, d257275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d255771 q = 1) (hb : d257276 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d255771, d257276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d255771, d257276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro64350 (p : Pattern) (ha : d255780 p = 1) (hb : d257490 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d255766 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d255646 q = 1) (hb : d257214 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d255646, d257214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64032 q ha hb
    | true =>
      simp only [d255646, d257214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d255767 q = 1) (hb : d257272 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d255767, d257272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d255767, d257272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d255647 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d255768 q = 1) (hb : d257273 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d255768, d257273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d255768, d257273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d255778 q = 1) (hb : d257274 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d255778, d257274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d255778, d257274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d255779 q = 1) (hb : d257275 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d255779, d257275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d255779, d257275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d255780 q = 1) (hb : d257490 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d255780, d257490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d255780, d257490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro64351 (p : Pattern) (ha : d255809 p = 1) (hb : d257536 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d255804 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d255680 q = 1) (hb : d257248 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d255680, d257248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64037 q ha hb
    | true =>
      simp only [d255680, d257248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d255805 q = 1) (hb : d257532 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d255805, d257532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d255805, d257532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d255681 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d255806 q = 1) (hb : d257533 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d255806, d257533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d255806, d257533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d255807 q = 1) (hb : d257534 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d255807, d257534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d255807, d257534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d255808 q = 1) (hb : d257535 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d255808, d257535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d255808, d257535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d255809 q = 1) (hb : d257536 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d255809, d257536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d255809, d257536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro64352 (p : Pattern) (ha : d255815 p = 1) (hb : d259893 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d255711 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d255772 q = 1) (hb : d257277 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d255772, d257277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64348 q ha hb
    | true =>
      simp only [d255772, d257277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64349 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d255774 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d255775 q = 1) (hb : d257278 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d255775, d257278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d255775, d257278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d255776 q = 1) (hb : d259883 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d255776, d259883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d255776, d259883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d255777 q = 1) (hb : d259884 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d255777, d259884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d255777, d259884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d255781 q = 1) (hb : d257491 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d255781, d257491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d255781, d257491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64350 q ha hb
  have h8 (q : Pattern) (ha : d255782 q = 1) (hb : d259885 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d255782, d259885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d255782, d259885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h9 (q : Pattern) (ha : d255783 q = 1) (hb : d259886 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d255783, d259886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d255783, d259886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h10 (q : Pattern) (ha : d255784 q = 1) (hb : d259887 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d255784, d259887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d255784, d259887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d255785 q = 1) (hb : d259888 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d255785, d259888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d255785, d259888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d255810 q = 1) (hb : d257537 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d255810, d257537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d255810, d257537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64351 q ha hb
  have h13 (q : Pattern) (ha : d255811 q = 1) (hb : d259889 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d255811, d259889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d255811, d259889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h14 (q : Pattern) (ha : d255812 q = 1) (hb : d259890 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d255812, d259890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d255812, d259890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h15 (q : Pattern) (ha : d255813 q = 1) (hb : d259891 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d255813, d259891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d255813, d259891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h16 (q : Pattern) (ha : d255814 q = 1) (hb : d259892 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d255814, d259892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d255814, d259892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d255815 q = 1) (hb : d259893 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d255815, d259893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d255815, d259893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro64353 (p : Pattern) (ha : d255821 p = 1) (hb : d259899 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d255696 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d255816 q = 1) (hb : d259894 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d255816, d259894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d255816, d259894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64352 q ha hb
  have h3 (q : Pattern) (ha : d255817 q = 1) (hb : d259895 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d255817, d259895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d255817, d259895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d255818 q = 1) (hb : d259896 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d255818, d259896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d255818, d259896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d255819 q = 1) (hb : d259897 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d255819, d259897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d255819, d259897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d255820 q = 1) (hb : d259898 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d255820, d259898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d255820, d259898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d255821 q = 1) (hb : d259899 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d255821, d259899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d255821, d259899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro64354 (p : Pattern) (ha : d255894 p = 1) (hb : d257393 p = 1) : d258783 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d255842 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d255848 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d255883 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d255750 q = 1) (hb : d257317 q = 1) : d258720 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d255750, d257317, d258720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64048 q ha hb
    | true =>
      simp only [d255750, d257317, d258720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64030 q ha hb
  have h5 (q : Pattern) (ha : d255884 q = 1) (hb : d257389 q = 1) : d258779 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d255884, d257389, d258779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d255884, d257389, d258779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d255890 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d255891 q = 1) (hb : d257390 q = 1) : d258780 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d255891, d257390, d258780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d255891, d257390, d258780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d255892 q = 1) (hb : d257391 q = 1) : d258781 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d255892, d257391, d258781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d255892, d257391, d258781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d255893 q = 1) (hb : d257392 q = 1) : d258782 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d255893, d257392, d258782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d255893, d257392, d258782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d255894 q = 1) (hb : d257393 q = 1) : d258783 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d255894, d257393, d258783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d255894, d257393, d258783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro64355 (p : Pattern) (ha : d255913 p = 1) (hb : d257400 p = 1) : d258790 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d255842 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d255848 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d255883 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d255750 q = 1) (hb : d257317 q = 1) : d258720 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d255750, d257317, d258720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64048 q ha hb
    | true =>
      simp only [d255750, d257317, d258720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64030 q ha hb
  have h4 (q : Pattern) (ha : d255884 q = 1) (hb : d257389 q = 1) : d258779 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d255884, d257389, d258779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d255884, d257389, d258779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d255890 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d255891 q = 1) (hb : d257390 q = 1) : d258780 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d255891, d257390, d258780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d255891, d257390, d258780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d255892 q = 1) (hb : d257391 q = 1) : d258781 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d255892, d257391, d258781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d255892, d257391, d258781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d255893 q = 1) (hb : d257392 q = 1) : d258782 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d255893, d257392, d258782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d255893, d257392, d258782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d255899 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d255903 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d255905 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d255766 q = 1) (hb : d257333 q = 1) : d258727 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d255766, d257333, d258727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64052 q ha hb
    | true =>
      simp only [d255766, d257333, d258727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64032 q ha hb
  have h13 (q : Pattern) (ha : d255906 q = 1) (hb : d257396 q = 1) : d258786 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d255906, d257396, d258786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d255906, d257396, d258786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d255909 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d255910 q = 1) (hb : d257397 q = 1) : d258787 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d255910, d257397, d258787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d255910, d257397, d258787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d255911 q = 1) (hb : d257398 q = 1) : d258788 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d255911, d257398, d258788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d255911, d257398, d258788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d255912 q = 1) (hb : d257399 q = 1) : d258789 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d255912, d257399, d258789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d255912, d257399, d258789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d255913 q = 1) (hb : d257400 q = 1) : d258790 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d255913, d257400, d258790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d255913, d257400, d258790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro64356 (p : Pattern) (ha : d255922 p = 1) (hb : d259902 p = 1) : d259008 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d255905 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d255766 q = 1) (hb : d257333 q = 1) : d258727 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d255766, d257333, d258727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64052 q ha hb
    | true =>
      simp only [d255766, d257333, d258727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64032 q ha hb
  have h3 (q : Pattern) (ha : d255906 q = 1) (hb : d257396 q = 1) : d258786 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d255906, d257396, d258786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d255906, d257396, d258786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d255909 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d255910 q = 1) (hb : d257397 q = 1) : d258787 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d255910, d257397, d258787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d255910, d257397, d258787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d255920 q = 1) (hb : d257398 q = 1) : d258788 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d255920, d257398, d258788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d255920, d257398, d258788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d255921 q = 1) (hb : d257399 q = 1) : d258789 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d255921, d257399, d258789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d255921, d257399, d258789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d255922 q = 1) (hb : d259902 q = 1) : d259008 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d255922, d259902, d259008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d255922, d259902, d259008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro64357 (p : Pattern) (ha : d255964 p = 1) (hb : d259912 p = 1) : d259054 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d255953 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d255804 q = 1) (hb : d257371 q = 1) : d258761 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d255804, d257371, d258761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64058 q ha hb
    | true =>
      simp only [d255804, d257371, d258761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64037 q ha hb
  have h3 (q : Pattern) (ha : d255954 q = 1) (hb : d259908 q = 1) : d259050 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d255954, d259908, d259050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d255954, d259908, d259050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d255960 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d255961 q = 1) (hb : d259909 q = 1) : d259051 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d255961, d259909, d259051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d255961, d259909, d259051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d255962 q = 1) (hb : d259910 q = 1) : d259052 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d255962, d259910, d259052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d255962, d259910, d259052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d255963 q = 1) (hb : d259911 q = 1) : d259053 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d255963, d259911, d259053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d255963, d259911, d259053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d255964 q = 1) (hb : d259912 q = 1) : d259054 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d255964, d259912, d259054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d255964, d259912, d259054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro64358 (p : Pattern) (ha : d255976 p = 1) (hb : d259918 p = 1) : d260097 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d255836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d255914 q = 1) (hb : d257401 q = 1) : d258791 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d255914, d257401, d258791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64354 q ha hb
    | true =>
      simp only [d255914, d257401, d258791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64355 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d255916 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d255917 q = 1) (hb : d257402 q = 1) : d258792 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d255917, d257402, d258792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d255917, d257402, d258792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d255918 q = 1) (hb : d259900 q = 1) : d260087 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d255918, d259900, d260087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d255918, d259900, d260087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d255919 q = 1) (hb : d259901 q = 1) : d260088 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d255919, d259901, d260088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d255919, d259901, d260088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d255923 q = 1) (hb : d259903 q = 1) : d259009 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d255923, d259903, d259009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d255923, d259903, d259009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64356 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d255925 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d255926 q = 1) (hb : d259904 q = 1) : d260089 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d255926, d259904, d260089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d255926, d259904, d260089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d255927 q = 1) (hb : d259905 q = 1) : d260090 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d255927, d259905, d260090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d255927, d259905, d260090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d255928 q = 1) (hb : d259906 q = 1) : d260091 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d255928, d259906, d260091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d255928, d259906, d260091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d255929 q = 1) (hb : d259907 q = 1) : d260092 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d255929, d259907, d260092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d255929, d259907, d260092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d255965 q = 1) (hb : d259913 q = 1) : d259055 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d255965, d259913, d259055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d255965, d259913, d259055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64357 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d255971 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d255972 q = 1) (hb : d259914 q = 1) : d260093 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d255972, d259914, d260093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d255972, d259914, d260093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d255973 q = 1) (hb : d259915 q = 1) : d260094 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d255973, d259915, d260094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d255973, d259915, d260094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d255974 q = 1) (hb : d259916 q = 1) : d260095 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d255974, d259916, d260095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d255974, d259916, d260095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d255975 q = 1) (hb : d259917 q = 1) : d260096 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d255975, d259917, d260096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d255975, d259917, d260096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d255976 q = 1) (hb : d259918 q = 1) : d260097 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d255976, d259918, d260097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d255976, d259918, d260097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro64359 (p : Pattern) (ha : d255982 p = 1) (hb : d259924 p = 1) : d260103 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d255977 q = 1) (hb : d259919 q = 1) : d260098 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d255977, d259919, d260098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d255977, d259919, d260098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64358 q ha hb
  have h2 (q : Pattern) (ha : d255978 q = 1) (hb : d259920 q = 1) : d260099 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d255978, d259920, d260099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d255978, d259920, d260099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d255979 q = 1) (hb : d259921 q = 1) : d260100 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d255979, d259921, d260100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d255979, d259921, d260100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d255980 q = 1) (hb : d259922 q = 1) : d260101 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d255980, d259922, d260101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d255980, d259922, d260101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d255981 q = 1) (hb : d259923 q = 1) : d260102 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d255981, d259923, d260102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d255981, d259923, d260102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d255982 q = 1) (hb : d259924 q = 1) : d260103 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d255982, d259924, d260103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d255982, d259924, d260103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro64360 (p : Pattern) (ha : d256101 p = 1) (hb : d257572 p = 1) : d258910 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d256027 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d256036 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d256090 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d256001 q = 1) (hb : d257567 q = 1) : d258833 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d256001, d257567, d258833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64092 q ha hb
    | true =>
      simp only [d256001, d257567, d258833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64093 q ha hb
  have h5 (q : Pattern) (ha : d256091 q = 1) (hb : d257568 q = 1) : d258906 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d256091, d257568, d258906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d256091, d257568, d258906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d256097 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d256098 q = 1) (hb : d257569 q = 1) : d258907 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d256098, d257569, d258907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d256098, d257569, d258907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d256099 q = 1) (hb : d257570 q = 1) : d258908 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d256099, d257570, d258908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d256099, d257570, d258908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d256100 q = 1) (hb : d257571 q = 1) : d258909 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d256100, d257571, d258909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d256100, d257571, d258909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d256101 q = 1) (hb : d257572 q = 1) : d258910 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d256101, d257572, d258910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d256101, d257572, d258910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro64361 (p : Pattern) (ha : d256122 p = 1) (hb : d257582 p = 1) : d258917 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d256027 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d256036 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d256090 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d256001 q = 1) (hb : d257567 q = 1) : d258833 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d256001, d257567, d258833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64092 q ha hb
    | true =>
      simp only [d256001, d257567, d258833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64093 q ha hb
  have h4 (q : Pattern) (ha : d256091 q = 1) (hb : d257568 q = 1) : d258906 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d256091, d257568, d258906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d256091, d257568, d258906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d256097 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d256098 q = 1) (hb : d257569 q = 1) : d258907 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d256098, d257569, d258907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d256098, d257569, d258907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d256099 q = 1) (hb : d257570 q = 1) : d258908 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d256099, d257570, d258908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d256099, d257570, d258908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d256100 q = 1) (hb : d257571 q = 1) : d258909 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d256100, d257571, d258909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d256100, d257571, d258909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d256107 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d256112 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d256114 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d256011 q = 1) (hb : d257577 q = 1) : d258849 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d256011, d257577, d258849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64095 q ha hb
    | true =>
      simp only [d256011, d257577, d258849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64096 q ha hb
  have h13 (q : Pattern) (ha : d256115 q = 1) (hb : d257578 q = 1) : d258913 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d256115, d257578, d258913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d256115, d257578, d258913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d256118 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d256119 q = 1) (hb : d257579 q = 1) : d258914 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d256119, d257579, d258914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d256119, d257579, d258914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d256120 q = 1) (hb : d257580 q = 1) : d258915 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d256120, d257580, d258915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d256120, d257580, d258915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d256121 q = 1) (hb : d257581 q = 1) : d258916 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d256121, d257581, d258916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d256121, d257581, d258916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d256122 q = 1) (hb : d257582 q = 1) : d258917 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d256122, d257582, d258917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d256122, d257582, d258917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro64362 (p : Pattern) (ha : d256142 p = 1) (hb : d259928 p = 1) : d260107 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d256114 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d256011 q = 1) (hb : d257577 q = 1) : d258849 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d256011, d257577, d258849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64095 q ha hb
    | true =>
      simp only [d256011, d257577, d258849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64096 q ha hb
  have h3 (q : Pattern) (ha : d256115 q = 1) (hb : d257578 q = 1) : d258913 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d256115, d257578, d258913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d256115, d257578, d258913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d256118 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d256119 q = 1) (hb : d257579 q = 1) : d258914 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d256119, d257579, d258914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d256119, d257579, d258914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d256140 q = 1) (hb : d257580 q = 1) : d258915 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d256140, d257580, d258915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d256140, d257580, d258915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d256141 q = 1) (hb : d257581 q = 1) : d258916 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d256141, d257581, d258916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d256141, d257581, d258916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d256142 q = 1) (hb : d259928 q = 1) : d260107 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d256142, d259928, d260107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d256142, d259928, d260107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro64363 (p : Pattern) (ha : d256210 p = 1) (hb : d259939 p = 1) : d260117 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d256194 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d256199 q = 1) (hb : d259934 q = 1) : d258887 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d256199, d259934, d258887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64130 q ha hb
    | true =>
      simp only [d256199, d259934, d258887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64133 q ha hb
  have h3 (q : Pattern) (ha : d256200 q = 1) (hb : d259935 q = 1) : d260113 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d256200, d259935, d260113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d256200, d259935, d260113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d256206 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d256207 q = 1) (hb : d259936 q = 1) : d260114 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d256207, d259936, d260114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d256207, d259936, d260114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d256208 q = 1) (hb : d259937 q = 1) : d260115 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d256208, d259937, d260115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d256208, d259937, d260115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d256209 q = 1) (hb : d259938 q = 1) : d260116 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d256209, d259938, d260116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d256209, d259938, d260116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d256210 q = 1) (hb : d259939 q = 1) : d260117 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d256210, d259939, d260117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d256210, d259939, d260117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro64364 (p : Pattern) (ha : d256223 p = 1) (hb : d259945 p = 1) : d260123 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d256019 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d256123 q = 1) (hb : d257583 q = 1) : d258918 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d256123, d257583, d258918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64360 q ha hb
    | true =>
      simp only [d256123, d257583, d258918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64361 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d256136 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d256137 q = 1) (hb : d257584 q = 1) : d258919 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d256137, d257584, d258919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d256137, d257584, d258919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d256138 q = 1) (hb : d259926 q = 1) : d260105 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d256138, d259926, d260105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d256138, d259926, d260105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d256139 q = 1) (hb : d259927 q = 1) : d260106 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d256139, d259927, d260106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d256139, d259927, d260106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d256143 q = 1) (hb : d259929 q = 1) : d260108 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d256143, d259929, d260108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d256143, d259929, d260108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64362 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d256145 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d256146 q = 1) (hb : d259930 q = 1) : d260109 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d256146, d259930, d260109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d256146, d259930, d260109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d256147 q = 1) (hb : d259931 q = 1) : d260110 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d256147, d259931, d260110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d256147, d259931, d260110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d256148 q = 1) (hb : d259932 q = 1) : d260111 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d256148, d259932, d260111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d256148, d259932, d260111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d256149 q = 1) (hb : d259933 q = 1) : d260112 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d256149, d259933, d260112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d256149, d259933, d260112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d256211 q = 1) (hb : d259940 q = 1) : d260118 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d256211, d259940, d260118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d256211, d259940, d260118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64363 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d256218 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d256219 q = 1) (hb : d259941 q = 1) : d260119 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d256219, d259941, d260119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d256219, d259941, d260119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d256220 q = 1) (hb : d259942 q = 1) : d260120 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d256220, d259942, d260120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d256220, d259942, d260120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d256221 q = 1) (hb : d259943 q = 1) : d260121 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d256221, d259943, d260121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d256221, d259943, d260121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d256222 q = 1) (hb : d259944 q = 1) : d260122 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d256222, d259944, d260122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d256222, d259944, d260122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d256223 q = 1) (hb : d259945 q = 1) : d260123 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d256223, d259945, d260123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d256223, d259945, d260123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro64365 (p : Pattern) (ha : d256229 p = 1) (hb : d259951 p = 1) : d260129 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d256224 q = 1) (hb : d259946 q = 1) : d260124 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d256224, d259946, d260124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d256224, d259946, d260124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64364 q ha hb
  have h2 (q : Pattern) (ha : d256225 q = 1) (hb : d259947 q = 1) : d260125 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d256225, d259947, d260125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d256225, d259947, d260125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d256226 q = 1) (hb : d259948 q = 1) : d260126 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d256226, d259948, d260126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d256226, d259948, d260126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d256227 q = 1) (hb : d259949 q = 1) : d260127 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d256227, d259949, d260127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d256227, d259949, d260127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d256228 q = 1) (hb : d259950 q = 1) : d260128 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d256228, d259950, d260128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d256228, d259950, d260128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d256229 q = 1) (hb : d259951 q = 1) : d260129 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d256229, d259951, d260129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d256229, d259951, d260129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro64366 (p : Pattern) (ha : d256397 p = 1) (hb : d257839 p = 1) : d259091 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d256326 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d256335 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d256386 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d256300 q = 1) (hb : d257834 q = 1) : d259086 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d256300, d257834, d259086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64147 q ha hb
    | true =>
      simp only [d256300, d257834, d259086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64148 q ha hb
  have h5 (q : Pattern) (ha : d256387 q = 1) (hb : d257835 q = 1) : d259087 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d256387, d257835, d259087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d256387, d257835, d259087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d256393 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d256394 q = 1) (hb : d257836 q = 1) : d259088 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d256394, d257836, d259088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d256394, d257836, d259088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d256395 q = 1) (hb : d257837 q = 1) : d259089 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d256395, d257837, d259089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d256395, d257837, d259089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d256396 q = 1) (hb : d257838 q = 1) : d259090 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d256396, d257838, d259090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d256396, d257838, d259090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d256397 q = 1) (hb : d257839 q = 1) : d259091 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d256397, d257839, d259091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d256397, d257839, d259091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro64367 (p : Pattern) (ha : d256418 p = 1) (hb : d257849 p = 1) : d259101 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d256326 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d256335 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d256386 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d256300 q = 1) (hb : d257834 q = 1) : d259086 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d256300, d257834, d259086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64147 q ha hb
    | true =>
      simp only [d256300, d257834, d259086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64148 q ha hb
  have h4 (q : Pattern) (ha : d256387 q = 1) (hb : d257835 q = 1) : d259087 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d256387, d257835, d259087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d256387, d257835, d259087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d256393 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d256394 q = 1) (hb : d257836 q = 1) : d259088 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d256394, d257836, d259088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d256394, d257836, d259088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d256395 q = 1) (hb : d257837 q = 1) : d259089 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d256395, d257837, d259089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d256395, d257837, d259089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d256396 q = 1) (hb : d257838 q = 1) : d259090 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d256396, d257838, d259090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d256396, d257838, d259090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d256403 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d256408 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d256410 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d256310 q = 1) (hb : d257844 q = 1) : d259096 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d256310, d257844, d259096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64150 q ha hb
    | true =>
      simp only [d256310, d257844, d259096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64151 q ha hb
  have h13 (q : Pattern) (ha : d256411 q = 1) (hb : d257845 q = 1) : d259097 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d256411, d257845, d259097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d256411, d257845, d259097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d256414 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d256415 q = 1) (hb : d257846 q = 1) : d259098 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d256415, d257846, d259098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d256415, d257846, d259098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d256416 q = 1) (hb : d257847 q = 1) : d259099 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d256416, d257847, d259099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d256416, d257847, d259099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d256417 q = 1) (hb : d257848 q = 1) : d259100 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d256417, d257848, d259100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d256417, d257848, d259100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d256418 q = 1) (hb : d257849 q = 1) : d259101 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d256418, d257849, d259101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d256418, d257849, d259101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro64368 (p : Pattern) (ha : d256438 p = 1) (hb : d259956 p = 1) : d260134 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d256410 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d256310 q = 1) (hb : d257844 q = 1) : d259096 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d256310, d257844, d259096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64150 q ha hb
    | true =>
      simp only [d256310, d257844, d259096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64151 q ha hb
  have h3 (q : Pattern) (ha : d256411 q = 1) (hb : d257845 q = 1) : d259097 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d256411, d257845, d259097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d256411, d257845, d259097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d256414 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d256415 q = 1) (hb : d257846 q = 1) : d259098 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d256415, d257846, d259098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d256415, d257846, d259098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d256436 q = 1) (hb : d257847 q = 1) : d259099 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d256436, d257847, d259099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d256436, d257847, d259099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d256437 q = 1) (hb : d257848 q = 1) : d259100 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d256437, d257848, d259100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d256437, d257848, d259100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d256438 q = 1) (hb : d259956 q = 1) : d260134 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d256438, d259956, d260134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d256438, d259956, d260134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro64369 (p : Pattern) (ha : d256545 p = 1) (hb : d259967 p = 1) : d260145 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d256529 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d256534 q = 1) (hb : d259962 q = 1) : d260140 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d256534, d259962, d260140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64187 q ha hb
    | true =>
      simp only [d256534, d259962, d260140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64190 q ha hb
  have h3 (q : Pattern) (ha : d256535 q = 1) (hb : d259963 q = 1) : d260141 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d256535, d259963, d260141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d256535, d259963, d260141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d256541 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d256542 q = 1) (hb : d259964 q = 1) : d260142 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d256542, d259964, d260142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d256542, d259964, d260142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d256543 q = 1) (hb : d259965 q = 1) : d260143 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d256543, d259965, d260143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d256543, d259965, d260143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d256544 q = 1) (hb : d259966 q = 1) : d260144 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d256544, d259966, d260144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d256544, d259966, d260144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d256545 q = 1) (hb : d259967 q = 1) : d260145 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d256545, d259967, d260145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d256545, d259967, d260145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro64370 (p : Pattern) (ha : d256558 p = 1) (hb : d259973 p = 1) : d260151 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d256318 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d256419 q = 1) (hb : d257850 q = 1) : d259102 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d256419, d257850, d259102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64366 q ha hb
    | true =>
      simp only [d256419, d257850, d259102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64367 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d256432 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d256433 q = 1) (hb : d257851 q = 1) : d259103 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d256433, d257851, d259103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d256433, d257851, d259103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d256434 q = 1) (hb : d259954 q = 1) : d260132 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d256434, d259954, d260132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d256434, d259954, d260132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d256435 q = 1) (hb : d259955 q = 1) : d260133 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d256435, d259955, d260133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d256435, d259955, d260133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d256439 q = 1) (hb : d259957 q = 1) : d260135 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d256439, d259957, d260135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d256439, d259957, d260135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64368 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d256441 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d256442 q = 1) (hb : d259958 q = 1) : d260136 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d256442, d259958, d260136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d256442, d259958, d260136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d256443 q = 1) (hb : d259959 q = 1) : d260137 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d256443, d259959, d260137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d256443, d259959, d260137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d256444 q = 1) (hb : d259960 q = 1) : d260138 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d256444, d259960, d260138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d256444, d259960, d260138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d256445 q = 1) (hb : d259961 q = 1) : d260139 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d256445, d259961, d260139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d256445, d259961, d260139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d256546 q = 1) (hb : d259968 q = 1) : d260146 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d256546, d259968, d260146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d256546, d259968, d260146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64369 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d256553 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d256554 q = 1) (hb : d259969 q = 1) : d260147 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d256554, d259969, d260147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d256554, d259969, d260147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d256555 q = 1) (hb : d259970 q = 1) : d260148 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d256555, d259970, d260148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d256555, d259970, d260148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d256556 q = 1) (hb : d259971 q = 1) : d260149 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d256556, d259971, d260149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d256556, d259971, d260149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d256557 q = 1) (hb : d259972 q = 1) : d260150 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d256557, d259972, d260150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d256557, d259972, d260150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d256558 q = 1) (hb : d259973 q = 1) : d260151 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d256558, d259973, d260151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d256558, d259973, d260151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro64371 (p : Pattern) (ha : d256564 p = 1) (hb : d259979 p = 1) : d260157 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d256559 q = 1) (hb : d259974 q = 1) : d260152 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d256559, d259974, d260152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d256559, d259974, d260152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64370 q ha hb
  have h2 (q : Pattern) (ha : d256560 q = 1) (hb : d259975 q = 1) : d260153 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d256560, d259975, d260153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d256560, d259975, d260153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d256561 q = 1) (hb : d259976 q = 1) : d260154 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d256561, d259976, d260154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d256561, d259976, d260154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d256562 q = 1) (hb : d259977 q = 1) : d260155 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d256562, d259977, d260155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d256562, d259977, d260155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d256563 q = 1) (hb : d259978 q = 1) : d260156 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d256563, d259978, d260156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d256563, d259978, d260156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d256564 q = 1) (hb : d259979 q = 1) : d260157 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d256564, d259979, d260157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d256564, d259979, d260157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro64372 (p : Pattern) (ha : d256728 p = 1) (hb : d258152 p = 1) : d259353 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d256670 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d256679 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d256717 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d256644 q = 1) (hb : d258147 q = 1) : d259348 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d256644, d258147, d259348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64208 q ha hb
    | true =>
      simp only [d256644, d258147, d259348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64209 q ha hb
  have h5 (q : Pattern) (ha : d256718 q = 1) (hb : d258148 q = 1) : d259349 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d256718, d258148, d259349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d256718, d258148, d259349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d256724 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d256725 q = 1) (hb : d258149 q = 1) : d259350 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d256725, d258149, d259350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d256725, d258149, d259350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d256726 q = 1) (hb : d258150 q = 1) : d259351 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d256726, d258150, d259351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d256726, d258150, d259351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d256727 q = 1) (hb : d258151 q = 1) : d259352 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d256727, d258151, d259352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d256727, d258151, d259352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d256728 q = 1) (hb : d258152 q = 1) : d259353 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d256728, d258152, d259353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d256728, d258152, d259353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro64373 (p : Pattern) (ha : d256749 p = 1) (hb : d258162 p = 1) : d259363 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d256670 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d256679 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d256717 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d256644 q = 1) (hb : d258147 q = 1) : d259348 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d256644, d258147, d259348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64208 q ha hb
    | true =>
      simp only [d256644, d258147, d259348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64209 q ha hb
  have h4 (q : Pattern) (ha : d256718 q = 1) (hb : d258148 q = 1) : d259349 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d256718, d258148, d259349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d256718, d258148, d259349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d256724 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d256725 q = 1) (hb : d258149 q = 1) : d259350 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d256725, d258149, d259350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d256725, d258149, d259350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d256726 q = 1) (hb : d258150 q = 1) : d259351 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d256726, d258150, d259351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d256726, d258150, d259351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d256727 q = 1) (hb : d258151 q = 1) : d259352 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d256727, d258151, d259352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d256727, d258151, d259352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d256734 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d256739 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d256741 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d256654 q = 1) (hb : d258157 q = 1) : d259358 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d256654, d258157, d259358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64211 q ha hb
    | true =>
      simp only [d256654, d258157, d259358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64212 q ha hb
  have h13 (q : Pattern) (ha : d256742 q = 1) (hb : d258158 q = 1) : d259359 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d256742, d258158, d259359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d256742, d258158, d259359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d256745 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d256746 q = 1) (hb : d258159 q = 1) : d259360 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d256746, d258159, d259360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d256746, d258159, d259360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d256747 q = 1) (hb : d258160 q = 1) : d259361 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d256747, d258160, d259361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d256747, d258160, d259361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d256748 q = 1) (hb : d258161 q = 1) : d259362 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d256748, d258161, d259362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d256748, d258161, d259362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d256749 q = 1) (hb : d258162 q = 1) : d259363 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d256749, d258162, d259363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d256749, d258162, d259363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro64374 (p : Pattern) (ha : d256769 p = 1) (hb : d259985 p = 1) : d260163 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d256741 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d256654 q = 1) (hb : d258157 q = 1) : d259358 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d256654, d258157, d259358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64211 q ha hb
    | true =>
      simp only [d256654, d258157, d259358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64212 q ha hb
  have h3 (q : Pattern) (ha : d256742 q = 1) (hb : d258158 q = 1) : d259359 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d256742, d258158, d259359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d256742, d258158, d259359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d256745 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d256746 q = 1) (hb : d258159 q = 1) : d259360 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d256746, d258159, d259360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d256746, d258159, d259360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d256767 q = 1) (hb : d258160 q = 1) : d259361 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d256767, d258160, d259361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d256767, d258160, d259361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d256768 q = 1) (hb : d258161 q = 1) : d259362 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d256768, d258161, d259362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d256768, d258161, d259362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d256769 q = 1) (hb : d259985 q = 1) : d260163 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d256769, d259985, d260163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d256769, d259985, d260163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro64375 (p : Pattern) (ha : d256872 p = 1) (hb : d259996 p = 1) : d260174 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d256856 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d256861 q = 1) (hb : d259991 q = 1) : d260169 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d256861, d259991, d260169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64247 q ha hb
    | true =>
      simp only [d256861, d259991, d260169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64250 q ha hb
  have h3 (q : Pattern) (ha : d256862 q = 1) (hb : d259992 q = 1) : d260170 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d256862, d259992, d260170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d256862, d259992, d260170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d256868 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d256869 q = 1) (hb : d259993 q = 1) : d260171 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d256869, d259993, d260171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d256869, d259993, d260171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d256870 q = 1) (hb : d259994 q = 1) : d260172 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d256870, d259994, d260172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d256870, d259994, d260172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d256871 q = 1) (hb : d259995 q = 1) : d260173 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d256871, d259995, d260173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d256871, d259995, d260173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d256872 q = 1) (hb : d259996 q = 1) : d260174 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d256872, d259996, d260174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d256872, d259996, d260174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro64376 (p : Pattern) (ha : d256885 p = 1) (hb : d260002 p = 1) : d260180 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d256662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d256750 q = 1) (hb : d258163 q = 1) : d259364 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d256750, d258163, d259364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64372 q ha hb
    | true =>
      simp only [d256750, d258163, d259364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64373 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d256763 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d256764 q = 1) (hb : d258164 q = 1) : d259365 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d256764, d258164, d259365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d256764, d258164, d259365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d256765 q = 1) (hb : d259983 q = 1) : d260161 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d256765, d259983, d260161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d256765, d259983, d260161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d256766 q = 1) (hb : d259984 q = 1) : d260162 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d256766, d259984, d260162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d256766, d259984, d260162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d256770 q = 1) (hb : d259986 q = 1) : d260164 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d256770, d259986, d260164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d256770, d259986, d260164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64374 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d256772 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d256773 q = 1) (hb : d259987 q = 1) : d260165 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d256773, d259987, d260165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d256773, d259987, d260165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d256774 q = 1) (hb : d259988 q = 1) : d260166 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d256774, d259988, d260166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d256774, d259988, d260166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d256775 q = 1) (hb : d259989 q = 1) : d260167 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d256775, d259989, d260167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d256775, d259989, d260167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d256776 q = 1) (hb : d259990 q = 1) : d260168 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d256776, d259990, d260168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d256776, d259990, d260168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d256873 q = 1) (hb : d259997 q = 1) : d260175 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d256873, d259997, d260175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d256873, d259997, d260175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64375 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d256880 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d256881 q = 1) (hb : d259998 q = 1) : d260176 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d256881, d259998, d260176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d256881, d259998, d260176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d256882 q = 1) (hb : d259999 q = 1) : d260177 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d256882, d259999, d260177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d256882, d259999, d260177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d256883 q = 1) (hb : d260000 q = 1) : d260178 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d256883, d260000, d260178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d256883, d260000, d260178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d256884 q = 1) (hb : d260001 q = 1) : d260179 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d256884, d260001, d260179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d256884, d260001, d260179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d256885 q = 1) (hb : d260002 q = 1) : d260180 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d256885, d260002, d260180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d256885, d260002, d260180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro64377 (p : Pattern) (ha : d256891 p = 1) (hb : d260008 p = 1) : d260186 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d256886 q = 1) (hb : d260003 q = 1) : d260181 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d256886, d260003, d260181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d256886, d260003, d260181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64376 q ha hb
  have h2 (q : Pattern) (ha : d256887 q = 1) (hb : d260004 q = 1) : d260182 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d256887, d260004, d260182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d256887, d260004, d260182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d256888 q = 1) (hb : d260005 q = 1) : d260183 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d256888, d260005, d260183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d256888, d260005, d260183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d256889 q = 1) (hb : d260006 q = 1) : d260184 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d256889, d260006, d260184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d256889, d260006, d260184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d256890 q = 1) (hb : d260007 q = 1) : d260185 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d256890, d260007, d260185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d256890, d260007, d260185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d256891 q = 1) (hb : d260008 q = 1) : d260186 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d256891, d260008, d260186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d256891, d260008, d260186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro64378 (p : Pattern) (ha : d257003 p = 1) (hb : d258445 p = 1) : d259635 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d256969 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d256978 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d256992 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d256943 q = 1) (hb : d258440 q = 1) : d259630 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d256943, d258440, d259630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64264 q ha hb
    | true =>
      simp only [d256943, d258440, d259630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64265 q ha hb
  have h5 (q : Pattern) (ha : d256993 q = 1) (hb : d258441 q = 1) : d259631 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d256993, d258441, d259631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d256993, d258441, d259631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d256999 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d257000 q = 1) (hb : d258442 q = 1) : d259632 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d257000, d258442, d259632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d257000, d258442, d259632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d257001 q = 1) (hb : d258443 q = 1) : d259633 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d257001, d258443, d259633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d257001, d258443, d259633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d257002 q = 1) (hb : d258444 q = 1) : d259634 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d257002, d258444, d259634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d257002, d258444, d259634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d257003 q = 1) (hb : d258445 q = 1) : d259635 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d257003, d258445, d259635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d257003, d258445, d259635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro64379 (p : Pattern) (ha : d257024 p = 1) (hb : d258455 p = 1) : d259645 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d256969 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d256978 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d256992 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d256943 q = 1) (hb : d258440 q = 1) : d259630 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d256943, d258440, d259630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64264 q ha hb
    | true =>
      simp only [d256943, d258440, d259630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64265 q ha hb
  have h4 (q : Pattern) (ha : d256993 q = 1) (hb : d258441 q = 1) : d259631 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d256993, d258441, d259631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d256993, d258441, d259631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d256999 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d257000 q = 1) (hb : d258442 q = 1) : d259632 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d257000, d258442, d259632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d257000, d258442, d259632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d257001 q = 1) (hb : d258443 q = 1) : d259633 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d257001, d258443, d259633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d257001, d258443, d259633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d257002 q = 1) (hb : d258444 q = 1) : d259634 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d257002, d258444, d259634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d257002, d258444, d259634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d257009 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d257014 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d257016 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d256953 q = 1) (hb : d258450 q = 1) : d259640 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d256953, d258450, d259640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64267 q ha hb
    | true =>
      simp only [d256953, d258450, d259640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64268 q ha hb
  have h13 (q : Pattern) (ha : d257017 q = 1) (hb : d258451 q = 1) : d259641 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d257017, d258451, d259641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d257017, d258451, d259641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d257020 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d257021 q = 1) (hb : d258452 q = 1) : d259642 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d257021, d258452, d259642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d257021, d258452, d259642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d257022 q = 1) (hb : d258453 q = 1) : d259643 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d257022, d258453, d259643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d257022, d258453, d259643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d257023 q = 1) (hb : d258454 q = 1) : d259644 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d257023, d258454, d259644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d257023, d258454, d259644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d257024 q = 1) (hb : d258455 q = 1) : d259645 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d257024, d258455, d259645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d257024, d258455, d259645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro64380 (p : Pattern) (ha : d257044 p = 1) (hb : d260015 p = 1) : d260193 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d257016 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d256953 q = 1) (hb : d258450 q = 1) : d259640 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d256953, d258450, d259640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64267 q ha hb
    | true =>
      simp only [d256953, d258450, d259640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64268 q ha hb
  have h3 (q : Pattern) (ha : d257017 q = 1) (hb : d258451 q = 1) : d259641 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d257017, d258451, d259641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d257017, d258451, d259641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d257020 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d257021 q = 1) (hb : d258452 q = 1) : d259642 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d257021, d258452, d259642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d257021, d258452, d259642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d257042 q = 1) (hb : d258453 q = 1) : d259643 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d257042, d258453, d259643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d257042, d258453, d259643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d257043 q = 1) (hb : d258454 q = 1) : d259644 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d257043, d258454, d259644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d257043, d258454, d259644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d257044 q = 1) (hb : d260015 q = 1) : d260193 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d257044, d260015, d260193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d257044, d260015, d260193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro64381 (p : Pattern) (ha : d257115 p = 1) (hb : d260026 p = 1) : d260204 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d257099 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d257104 q = 1) (hb : d260021 q = 1) : d260199 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d257104, d260021, d260199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64300 q ha hb
    | true =>
      simp only [d257104, d260021, d260199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64303 q ha hb
  have h3 (q : Pattern) (ha : d257105 q = 1) (hb : d260022 q = 1) : d260200 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d257105, d260022, d260200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d257105, d260022, d260200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d257111 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d257112 q = 1) (hb : d260023 q = 1) : d260201 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d257112, d260023, d260201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d257112, d260023, d260201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d257113 q = 1) (hb : d260024 q = 1) : d260202 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d257113, d260024, d260202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d257113, d260024, d260202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d257114 q = 1) (hb : d260025 q = 1) : d260203 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d257114, d260025, d260203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d257114, d260025, d260203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d257115 q = 1) (hb : d260026 q = 1) : d260204 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d257115, d260026, d260204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d257115, d260026, d260204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro64382 (p : Pattern) (ha : d257128 p = 1) (hb : d260032 p = 1) : d260210 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d256961 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d257025 q = 1) (hb : d258456 q = 1) : d259646 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d257025, d258456, d259646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64378 q ha hb
    | true =>
      simp only [d257025, d258456, d259646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64379 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d257038 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d257039 q = 1) (hb : d258457 q = 1) : d259647 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d257039, d258457, d259647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d257039, d258457, d259647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d257040 q = 1) (hb : d260013 q = 1) : d260191 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d257040, d260013, d260191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d257040, d260013, d260191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d257041 q = 1) (hb : d260014 q = 1) : d260192 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d257041, d260014, d260192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d257041, d260014, d260192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d257045 q = 1) (hb : d260016 q = 1) : d260194 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d257045, d260016, d260194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d257045, d260016, d260194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64380 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d257047 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d257048 q = 1) (hb : d260017 q = 1) : d260195 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d257048, d260017, d260195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d257048, d260017, d260195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d257049 q = 1) (hb : d260018 q = 1) : d260196 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d257049, d260018, d260196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d257049, d260018, d260196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d257050 q = 1) (hb : d260019 q = 1) : d260197 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d257050, d260019, d260197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d257050, d260019, d260197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d257051 q = 1) (hb : d260020 q = 1) : d260198 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d257051, d260020, d260198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d257051, d260020, d260198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d257116 q = 1) (hb : d260027 q = 1) : d260205 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d257116, d260027, d260205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d257116, d260027, d260205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64381 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d257123 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d257124 q = 1) (hb : d260028 q = 1) : d260206 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d257124, d260028, d260206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d257124, d260028, d260206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d257125 q = 1) (hb : d260029 q = 1) : d260207 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d257125, d260029, d260207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d257125, d260029, d260207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d257126 q = 1) (hb : d260030 q = 1) : d260208 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d257126, d260030, d260208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d257126, d260030, d260208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d257127 q = 1) (hb : d260031 q = 1) : d260209 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d257127, d260031, d260209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d257127, d260031, d260209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d257128 q = 1) (hb : d260032 q = 1) : d260210 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d257128, d260032, d260210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d257128, d260032, d260210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro64383 (p : Pattern) (ha : d257134 p = 1) (hb : d260038 p = 1) : d260216 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d257129 q = 1) (hb : d260033 q = 1) : d260211 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d257129, d260033, d260211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d257129, d260033, d260211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64382 q ha hb
  have h2 (q : Pattern) (ha : d257130 q = 1) (hb : d260034 q = 1) : d260212 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d257130, d260034, d260212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d257130, d260034, d260212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d257131 q = 1) (hb : d260035 q = 1) : d260213 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d257131, d260035, d260213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d257131, d260035, d260213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d257132 q = 1) (hb : d260036 q = 1) : d260214 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d257132, d260036, d260214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d257132, d260036, d260214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d257133 q = 1) (hb : d260037 q = 1) : d260215 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d257133, d260037, d260215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d257133, d260037, d260215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d257134 q = 1) (hb : d260038 q = 1) : d260216 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d257134, d260038, d260216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d257134, d260038, d260216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro64384 (p : Pattern) (ha : d257140 p = 1) (hb : d260044 p = 1) : d260222 p = 1 := by
  have h0 (q : Pattern) (ha : d255983 q = 1) (hb : d259925 q = 1) : d260104 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d255983, d259925, d260104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64353 q ha hb
    | true =>
      simp only [d255983, d259925, d260104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64359 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d256230 q = 1) (hb : d259952 q = 1) : d260130 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d256230, d259952, d260130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d256230, d259952, d260130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64365 q ha hb
  have h3 (q : Pattern) (ha : d256231 q = 1) (hb : d259953 q = 1) : d260131 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d256231, d259953, d260131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d256231, d259953, d260131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d256565 q = 1) (hb : d259980 q = 1) : d260158 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d256565, d259980, d260158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d256565, d259980, d260158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64371 q ha hb
  have h5 (q : Pattern) (ha : d256566 q = 1) (hb : d259981 q = 1) : d260159 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d256566, d259981, d260159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d256566, d259981, d260159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d256567 q = 1) (hb : d259982 q = 1) : d260160 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d256567, d259982, d260160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d256567, d259982, d260160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d256892 q = 1) (hb : d260009 q = 1) : d260187 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d256892, d260009, d260187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d256892, d260009, d260187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64377 q ha hb
  have h8 (q : Pattern) (ha : d256893 q = 1) (hb : d260010 q = 1) : d260188 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d256893, d260010, d260188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d256893, d260010, d260188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d256894 q = 1) (hb : d260011 q = 1) : d260189 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d256894, d260011, d260189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d256894, d260011, d260189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d256895 q = 1) (hb : d260012 q = 1) : d260190 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d256895, d260012, d260190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d256895, d260012, d260190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d257135 q = 1) (hb : d260039 q = 1) : d260217 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d257135, d260039, d260217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d257135, d260039, d260217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64383 q ha hb
  have h12 (q : Pattern) (ha : d257136 q = 1) (hb : d260040 q = 1) : d260218 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d257136, d260040, d260218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d257136, d260040, d260218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d257137 q = 1) (hb : d260041 q = 1) : d260219 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d257137, d260041, d260219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d257137, d260041, d260219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d257138 q = 1) (hb : d260042 q = 1) : d260220 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d257138, d260042, d260220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d257138, d260042, d260220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d257139 q = 1) (hb : d260043 q = 1) : d260221 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d257139, d260043, d260221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d257139, d260043, d260221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d257140 q = 1) (hb : d260044 q = 1) : d260222 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d257140, d260044, d260222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d257140, d260044, d260222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro64385 (p : Pattern) (ha : d257146 p = 1) (hb : d260050 p = 1) : d260228 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d257141 q = 1) (hb : d260045 q = 1) : d260223 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d257141, d260045, d260223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64384 q ha hb
    | true =>
      simp only [d257141, d260045, d260223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d257142 q = 1) (hb : d260046 q = 1) : d260224 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d257142, d260046, d260224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d257142, d260046, d260224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d257143 q = 1) (hb : d260047 q = 1) : d260225 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d257143, d260047, d260225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d257143, d260047, d260225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d257144 q = 1) (hb : d260048 q = 1) : d260226 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d257144, d260048, d260226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d257144, d260048, d260226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d257145 q = 1) (hb : d260049 q = 1) : d260227 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d257145, d260049, d260227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d257145, d260049, d260227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d257146 q = 1) (hb : d260050 q = 1) : d260228 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d257146, d260050, d260228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d257146, d260050, d260228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro64386 (p : Pattern) (ha : d257152 p = 1) (hb : d260056 p = 1) : d260234 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d257147 q = 1) (hb : d260051 q = 1) : d260229 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d257147, d260051, d260229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64385 q ha hb
    | true =>
      simp only [d257147, d260051, d260229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d257148 q = 1) (hb : d260052 q = 1) : d260230 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d257148, d260052, d260230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d257148, d260052, d260230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d257149 q = 1) (hb : d260053 q = 1) : d260231 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d257149, d260053, d260231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d257149, d260053, d260231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d257150 q = 1) (hb : d260054 q = 1) : d260232 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d257150, d260054, d260232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d257150, d260054, d260232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d257151 q = 1) (hb : d260055 q = 1) : d260233 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d257151, d260055, d260233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d257151, d260055, d260233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d257152 q = 1) (hb : d260056 q = 1) : d260234 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d257152, d260056, d260234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d257152, d260056, d260234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro64387 (p : Pattern) (ha : d257158 p = 1) (hb : d260062 p = 1) : d260240 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d257153 q = 1) (hb : d260057 q = 1) : d260235 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d257153, d260057, d260235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64386 q ha hb
    | true =>
      simp only [d257153, d260057, d260235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d257154 q = 1) (hb : d260058 q = 1) : d260236 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d257154, d260058, d260236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d257154, d260058, d260236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d257155 q = 1) (hb : d260059 q = 1) : d260237 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d257155, d260059, d260237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d257155, d260059, d260237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d257156 q = 1) (hb : d260060 q = 1) : d260238 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d257156, d260060, d260238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d257156, d260060, d260238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d257157 q = 1) (hb : d260061 q = 1) : d260239 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d257157, d260061, d260239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d257157, d260061, d260239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d257158 q = 1) (hb : d260062 q = 1) : d260240 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d257158, d260062, d260240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d257158, d260062, d260240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro64388 (p : Pattern) (ha : d257164 p = 1) (hb : d260068 p = 1) : d260246 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d257159 q = 1) (hb : d260063 q = 1) : d260241 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d257159, d260063, d260241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64387 q ha hb
    | true =>
      simp only [d257159, d260063, d260241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d257160 q = 1) (hb : d260064 q = 1) : d260242 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d257160, d260064, d260242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d257160, d260064, d260242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d257161 q = 1) (hb : d260065 q = 1) : d260243 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d257161, d260065, d260243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d257161, d260065, d260243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d257162 q = 1) (hb : d260066 q = 1) : d260244 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d257162, d260066, d260244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d257162, d260066, d260244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d257163 q = 1) (hb : d260067 q = 1) : d260245 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d257163, d260067, d260245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d257163, d260067, d260245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d257164 q = 1) (hb : d260068 q = 1) : d260246 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d257164, d260068, d260246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d257164, d260068, d260246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro64389 (p : Pattern) (ha : d257170 p = 1) (hb : d260074 p = 1) : d260252 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d257165 q = 1) (hb : d260069 q = 1) : d260247 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d257165, d260069, d260247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64388 q ha hb
    | true =>
      simp only [d257165, d260069, d260247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d257166 q = 1) (hb : d260070 q = 1) : d260248 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d257166, d260070, d260248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d257166, d260070, d260248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d257167 q = 1) (hb : d260071 q = 1) : d260249 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d257167, d260071, d260249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d257167, d260071, d260249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d257168 q = 1) (hb : d260072 q = 1) : d260250 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d257168, d260072, d260250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d257168, d260072, d260250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d257169 q = 1) (hb : d260073 q = 1) : d260251 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d257169, d260073, d260251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d257169, d260073, d260251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d257170 q = 1) (hb : d260074 q = 1) : d260252 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d257170, d260074, d260252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d257170, d260074, d260252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro64390 (p : Pattern) (ha : d257176 p = 1) (hb : d260080 p = 1) : d260258 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d257171 q = 1) (hb : d260075 q = 1) : d260253 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d257171, d260075, d260253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64389 q ha hb
    | true =>
      simp only [d257171, d260075, d260253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d257172 q = 1) (hb : d260076 q = 1) : d260254 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d257172, d260076, d260254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d257172, d260076, d260254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d257173 q = 1) (hb : d260077 q = 1) : d260255 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d257173, d260077, d260255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d257173, d260077, d260255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d257174 q = 1) (hb : d260078 q = 1) : d260256 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d257174, d260078, d260256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d257174, d260078, d260256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d257175 q = 1) (hb : d260079 q = 1) : d260257 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d257175, d260079, d260257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d257175, d260079, d260257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d257176 q = 1) (hb : d260080 q = 1) : d260258 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d257176, d260080, d260258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d257176, d260080, d260258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro64391 (p : Pattern) (ha : d257182 p = 1) (hb : d260086 p = 1) : d260264 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d257177 q = 1) (hb : d260081 q = 1) : d260259 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d257177, d260081, d260259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64390 q ha hb
    | true =>
      simp only [d257177, d260081, d260259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d257178 q = 1) (hb : d260082 q = 1) : d260260 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d257178, d260082, d260260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d257178, d260082, d260260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d257179 q = 1) (hb : d260083 q = 1) : d260261 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d257179, d260083, d260261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d257179, d260083, d260261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d257180 q = 1) (hb : d260084 q = 1) : d260262 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d257180, d260084, d260262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d257180, d260084, d260262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d257181 q = 1) (hb : d260085 q = 1) : d260263 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d257181, d260085, d260263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d257181, d260085, d260263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d257182 q = 1) (hb : d260086 q = 1) : d260264 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d257182, d260086, d260264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d257182, d260086, d260264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro64392 (p : Pattern) (ha : d257269 p = 1) (hb : d260269 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d253608 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d253614 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d253641 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d257207 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d257265 q = 1) (hb : d260265 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d257265, d260265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d257265, d260265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d253531 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d257266 q = 1) (hb : d260266 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d257266, d260266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d257266, d260266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d257267 q = 1) (hb : d260267 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d257267, d260267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d257267, d260267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d257268 q = 1) (hb : d260268 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d257268, d260268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d257268, d260268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d257269 q = 1) (hb : d260269 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d257269, d260269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d257269, d260269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro64393 (p : Pattern) (ha : d257276 p = 1) (hb : d260274 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d253608 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d253614 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d253641 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d257207 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d257265 q = 1) (hb : d260265 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d257265, d260265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d257265, d260265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d253531 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d257266 q = 1) (hb : d260266 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d257266, d260266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d257266, d260266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d257267 q = 1) (hb : d260267 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d257267, d260267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d257267, d260267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d257268 q = 1) (hb : d260268 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d257268, d260268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d257268, d260268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d253678 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d253682 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d253684 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d257214 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d257272 q = 1) (hb : d260270 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d257272, d260270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d257272, d260270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d253538 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d257273 q = 1) (hb : d260271 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d257273, d260271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d257273, d260271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d257274 q = 1) (hb : d260272 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d257274, d260272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d257274, d260272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d257275 q = 1) (hb : d260273 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d257275, d260273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d257275, d260273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d257276 q = 1) (hb : d260274 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d257276, d260274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d257276, d260274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro64394 (p : Pattern) (ha : d257490 p = 1) (hb : d260281 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d253684 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d257214 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d257272 q = 1) (hb : d260270 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d257272, d260270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d257272, d260270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d253538 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d257273 q = 1) (hb : d260271 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d257273, d260271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d257273, d260271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d257274 q = 1) (hb : d260279 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d257274, d260279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d257274, d260279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d257275 q = 1) (hb : d260280 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d257275, d260280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d257275, d260280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d257490 q = 1) (hb : d260281 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d257490, d260281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d257490, d260281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro64395 (p : Pattern) (ha : d257536 p = 1) (hb : d260291 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d253724 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d257248 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d257532 q = 1) (hb : d260287 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d257532, d260287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d257532, d260287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d253572 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d257533 q = 1) (hb : d260288 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d257533, d260288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d257533, d260288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d257534 q = 1) (hb : d260289 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d257534, d260289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d257534, d260289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d257535 q = 1) (hb : d260290 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d257535, d260290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d257535, d260290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d257536 q = 1) (hb : d260291 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d257536, d260291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d257536, d260291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro64396 (p : Pattern) (ha : d259893 p = 1) (hb : d260297 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d253602 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d257277 q = 1) (hb : d260275 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d257277, d260275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64392 q ha hb
    | true =>
      simp only [d257277, d260275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64393 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d253694 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d257278 q = 1) (hb : d260276 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d257278, d260276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d257278, d260276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d259883 q = 1) (hb : d260277 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d259883, d260277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d259883, d260277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d259884 q = 1) (hb : d260278 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d259884, d260278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d259884, d260278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d257491 q = 1) (hb : d260282 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d257491, d260282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d257491, d260282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64394 q ha hb
  have h8 (q : Pattern) (ha : d259885 q = 1) (hb : d260283 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d259885, d260283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d259885, d260283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h9 (q : Pattern) (ha : d259886 q = 1) (hb : d260284 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d259886, d260284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d259886, d260284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d259887 q = 1) (hb : d260285 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d259887, d260285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d259887, d260285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d259888 q = 1) (hb : d260286 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d259888, d260286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d259888, d260286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d257537 q = 1) (hb : d260292 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d257537, d260292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d257537, d260292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64395 q ha hb
  have h13 (q : Pattern) (ha : d259889 q = 1) (hb : d260293 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d259889, d260293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d259889, d260293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h14 (q : Pattern) (ha : d259890 q = 1) (hb : d260294 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d259890, d260294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d259890, d260294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h15 (q : Pattern) (ha : d259891 q = 1) (hb : d260295 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d259891, d260295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d259891, d260295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h16 (q : Pattern) (ha : d259892 q = 1) (hb : d260296 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d259892, d260296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d259892, d260296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d259893 q = 1) (hb : d260297 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d259893, d260297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d259893, d260297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro64397 (p : Pattern) (ha : d259899 p = 1) (hb : d260303 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d253587 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d259894 q = 1) (hb : d260298 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d259894, d260298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d259894, d260298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64396 q ha hb
  have h3 (q : Pattern) (ha : d259895 q = 1) (hb : d260299 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d259895, d260299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d259895, d260299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d259896 q = 1) (hb : d260300 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d259896, d260300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d259896, d260300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d259897 q = 1) (hb : d260301 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d259897, d260301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d259897, d260301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d259898 q = 1) (hb : d260302 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d259898, d260302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d259898, d260302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d259899 q = 1) (hb : d260303 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d259899, d260303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d259899, d260303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro64398 (p : Pattern) (ha : d257393 p = 1) (hb : d260308 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d253781 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d253787 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d253822 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d257317 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d257389 q = 1) (hb : d260304 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d257389, d260304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d257389, d260304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d253856 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d257390 q = 1) (hb : d260305 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d257390, d260305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d257390, d260305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d257391 q = 1) (hb : d260306 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d257391, d260306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d257391, d260306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d257392 q = 1) (hb : d260307 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d257392, d260307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d257392, d260307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d257393 q = 1) (hb : d260308 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d257393, d260308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d257393, d260308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro64399 (p : Pattern) (ha : d257400 p = 1) (hb : d260313 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d253781 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d253787 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d253822 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d257317 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d257389 q = 1) (hb : d260304 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d257389, d260304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d257389, d260304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d253856 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d257390 q = 1) (hb : d260305 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d257390, d260305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d257390, d260305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d257391 q = 1) (hb : d260306 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d257391, d260306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d257391, d260306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d257392 q = 1) (hb : d260307 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d257392, d260307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d257392, d260307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d253865 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d253869 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d253871 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d257333 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d257396 q = 1) (hb : d260309 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d257396, d260309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d257396, d260309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d253877 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d257397 q = 1) (hb : d260310 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d257397, d260310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d257397, d260310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d257398 q = 1) (hb : d260311 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d257398, d260311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d257398, d260311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d257399 q = 1) (hb : d260312 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d257399, d260312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d257399, d260312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d257400 q = 1) (hb : d260313 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d257400, d260313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d257400, d260313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro64400 (p : Pattern) (ha : d259902 p = 1) (hb : d260320 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d253871 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d257333 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d257396 q = 1) (hb : d260309 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d257396, d260309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d257396, d260309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d253877 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d257397 q = 1) (hb : d260310 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d257397, d260310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d257397, d260310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d257398 q = 1) (hb : d260318 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d257398, d260318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d257398, d260318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d257399 q = 1) (hb : d260319 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d257399, d260319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d257399, d260319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d259902 q = 1) (hb : d260320 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d259902, d260320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d259902, d260320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro64401 (p : Pattern) (ha : d259912 p = 1) (hb : d260330 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d253921 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d257371 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d259908 q = 1) (hb : d260326 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d259908, d260326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d259908, d260326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d253947 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d259909 q = 1) (hb : d260327 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d259909, d260327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d259909, d260327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d259910 q = 1) (hb : d260328 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d259910, d260328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d259910, d260328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d259911 q = 1) (hb : d260329 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d259911, d260329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d259911, d260329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d259912 q = 1) (hb : d260330 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d259912, d260330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d259912, d260330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro64402 (p : Pattern) (ha : d259918 p = 1) (hb : d260336 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d253775 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d257401 q = 1) (hb : d260314 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d257401, d260314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64398 q ha hb
    | true =>
      simp only [d257401, d260314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64399 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d253884 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d257402 q = 1) (hb : d260315 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d257402, d260315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d257402, d260315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d259900 q = 1) (hb : d260316 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d259900, d260316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d259900, d260316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d259901 q = 1) (hb : d260317 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d259901, d260317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d259901, d260317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d259903 q = 1) (hb : d260321 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d259903, d260321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d259903, d260321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64400 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d253893 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d259904 q = 1) (hb : d260322 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d259904, d260322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d259904, d260322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d259905 q = 1) (hb : d260323 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d259905, d260323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d259905, d260323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d259906 q = 1) (hb : d260324 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d259906, d260324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d259906, d260324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d259907 q = 1) (hb : d260325 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d259907, d260325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d259907, d260325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d259913 q = 1) (hb : d260331 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d259913, d260331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d259913, d260331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64401 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d253958 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d259914 q = 1) (hb : d260332 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d259914, d260332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d259914, d260332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d259915 q = 1) (hb : d260333 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d259915, d260333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d259915, d260333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d259916 q = 1) (hb : d260334 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d259916, d260334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d259916, d260334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d259917 q = 1) (hb : d260335 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d259917, d260335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d259917, d260335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d259918 q = 1) (hb : d260336 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d259918, d260336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d259918, d260336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro64403 (p : Pattern) (ha : d259924 p = 1) (hb : d260342 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d259919 q = 1) (hb : d260337 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d259919, d260337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d259919, d260337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64402 q ha hb
  have h2 (q : Pattern) (ha : d259920 q = 1) (hb : d260338 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d259920, d260338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d259920, d260338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d259921 q = 1) (hb : d260339 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d259921, d260339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d259921, d260339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d259922 q = 1) (hb : d260340 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d259922, d260340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d259922, d260340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d259923 q = 1) (hb : d260341 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d259923, d260341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d259923, d260341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d259924 q = 1) (hb : d260342 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d259924, d260342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d259924, d260342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro64404 (p : Pattern) (ha : d257572 p = 1) (hb : d260348 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d254014 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d254023 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d254077 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d257567 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d257568 q = 1) (hb : d260344 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d257568, d260344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d257568, d260344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d254128 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d257569 q = 1) (hb : d260345 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d257569, d260345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d257569, d260345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d257570 q = 1) (hb : d260346 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d257570, d260346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d257570, d260346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d257571 q = 1) (hb : d260347 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d257571, d260347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d257571, d260347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d257572 q = 1) (hb : d260348 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d257572, d260348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d257572, d260348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro64405 (p : Pattern) (ha : d257582 p = 1) (hb : d260353 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d254014 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d254023 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d254077 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d257567 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d257568 q = 1) (hb : d260344 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d257568, d260344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d257568, d260344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d254128 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d257569 q = 1) (hb : d260345 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d257569, d260345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d257569, d260345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d257570 q = 1) (hb : d260346 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d257570, d260346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d257570, d260346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d257571 q = 1) (hb : d260347 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d257571, d260347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d257571, d260347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d254138 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d254143 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d254145 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d257577 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d257578 q = 1) (hb : d260349 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d257578, d260349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d257578, d260349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d254152 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d257579 q = 1) (hb : d260350 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d257579, d260350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d257579, d260350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d257580 q = 1) (hb : d260351 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d257580, d260351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d257580, d260351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d257581 q = 1) (hb : d260352 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d257581, d260352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d257581, d260352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d257582 q = 1) (hb : d260353 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d257582, d260353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d257582, d260353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro64406 (p : Pattern) (ha : d259928 p = 1) (hb : d260360 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d254145 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d257577 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d257578 q = 1) (hb : d260349 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d257578, d260349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d257578, d260349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d254152 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d257579 q = 1) (hb : d260350 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d257579, d260350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d257579, d260350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d257580 q = 1) (hb : d260358 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d257580, d260358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d257580, d260358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d257581 q = 1) (hb : d260359 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d257581, d260359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d257581, d260359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d259928 q = 1) (hb : d260360 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d259928, d260360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d259928, d260360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro64407 (p : Pattern) (ha : d259939 p = 1) (hb : d260370 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d254228 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d259934 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d259935 q = 1) (hb : d260366 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d259935, d260366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d259935, d260366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d254268 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d259936 q = 1) (hb : d260367 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d259936, d260367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d259936, d260367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d259937 q = 1) (hb : d260368 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d259937, d260368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d259937, d260368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d259938 q = 1) (hb : d260369 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d259938, d260369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d259938, d260369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d259939 q = 1) (hb : d260370 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d259939, d260370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d259939, d260370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro64408 (p : Pattern) (ha : d259945 p = 1) (hb : d260376 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d254006 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d257583 q = 1) (hb : d260354 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d257583, d260354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64404 q ha hb
    | true =>
      simp only [d257583, d260354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64405 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d254170 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d257584 q = 1) (hb : d260355 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d257584, d260355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d257584, d260355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d259926 q = 1) (hb : d260356 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d259926, d260356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d259926, d260356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d259927 q = 1) (hb : d260357 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d259927, d260357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d259927, d260357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d259929 q = 1) (hb : d260361 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d259929, d260361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d259929, d260361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64406 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d254179 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d259930 q = 1) (hb : d260362 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d259930, d260362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d259930, d260362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d259931 q = 1) (hb : d260363 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d259931, d260363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d259931, d260363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d259932 q = 1) (hb : d260364 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d259932, d260364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d259932, d260364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d259933 q = 1) (hb : d260365 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d259933, d260365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d259933, d260365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d259940 q = 1) (hb : d260371 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d259940, d260371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d259940, d260371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64407 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d254284 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d259941 q = 1) (hb : d260372 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d259941, d260372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d259941, d260372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d259942 q = 1) (hb : d260373 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d259942, d260373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d259942, d260373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d259943 q = 1) (hb : d260374 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d259943, d260374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d259943, d260374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d259944 q = 1) (hb : d260375 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d259944, d260375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d259944, d260375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d259945 q = 1) (hb : d260376 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d259945, d260376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d259945, d260376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro64409 (p : Pattern) (ha : d259951 p = 1) (hb : d260382 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d259946 q = 1) (hb : d260377 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d259946, d260377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d259946, d260377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64408 q ha hb
  have h2 (q : Pattern) (ha : d259947 q = 1) (hb : d260378 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d259947, d260378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d259947, d260378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d259948 q = 1) (hb : d260379 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d259948, d260379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d259948, d260379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d259949 q = 1) (hb : d260380 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d259949, d260380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d259949, d260380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d259950 q = 1) (hb : d260381 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d259950, d260381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d259950, d260381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d259951 q = 1) (hb : d260382 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d259951, d260382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d259951, d260382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro64410 (p : Pattern) (ha : d257839 p = 1) (hb : d260389 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d254392 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d254401 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d254452 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d257834 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d257835 q = 1) (hb : d260385 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d257835, d260385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d257835, d260385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d254545 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d257836 q = 1) (hb : d260386 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d257836, d260386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d257836, d260386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d257837 q = 1) (hb : d260387 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d257837, d260387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d257837, d260387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d257838 q = 1) (hb : d260388 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d257838, d260388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d257838, d260388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d257839 q = 1) (hb : d260389 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d257839, d260389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d257839, d260389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro64411 (p : Pattern) (ha : d257849 p = 1) (hb : d260394 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d254392 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d254401 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d254452 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d257834 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d257835 q = 1) (hb : d260385 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d257835, d260385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d257835, d260385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d254545 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d257836 q = 1) (hb : d260386 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d257836, d260386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d257836, d260386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d257837 q = 1) (hb : d260387 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d257837, d260387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d257837, d260387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d257838 q = 1) (hb : d260388 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d257838, d260388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d257838, d260388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d254555 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d254560 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d254562 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d257844 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d257845 q = 1) (hb : d260390 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d257845, d260390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d257845, d260390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d254569 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d257846 q = 1) (hb : d260391 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d257846, d260391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d257846, d260391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d257847 q = 1) (hb : d260392 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d257847, d260392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d257847, d260392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d257848 q = 1) (hb : d260393 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d257848, d260393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d257848, d260393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d257849 q = 1) (hb : d260394 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d257849, d260394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d257849, d260394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro64412 (p : Pattern) (ha : d259956 p = 1) (hb : d260401 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d254562 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d257844 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d257845 q = 1) (hb : d260390 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d257845, d260390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d257845, d260390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d254569 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d257846 q = 1) (hb : d260391 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d257846, d260391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d257846, d260391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d257847 q = 1) (hb : d260399 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d257847, d260399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d257847, d260399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d257848 q = 1) (hb : d260400 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d257848, d260400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d257848, d260400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d259956 q = 1) (hb : d260401 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d259956, d260401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d259956, d260401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro64413 (p : Pattern) (ha : d259967 p = 1) (hb : d260411 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d254684 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d259962 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d259963 q = 1) (hb : d260407 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d259963, d260407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d259963, d260407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d254743 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d259964 q = 1) (hb : d260408 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d259964, d260408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d259964, d260408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d259965 q = 1) (hb : d260409 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d259965, d260409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d259965, d260409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d259966 q = 1) (hb : d260410 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d259966, d260410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d259966, d260410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d259967 q = 1) (hb : d260411 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d259967, d260411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d259967, d260411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro64414 (p : Pattern) (ha : d259973 p = 1) (hb : d260417 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d254384 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d257850 q = 1) (hb : d260395 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d257850, d260395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64410 q ha hb
    | true =>
      simp only [d257850, d260395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64411 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d254587 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d257851 q = 1) (hb : d260396 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d257851, d260396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d257851, d260396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d259954 q = 1) (hb : d260397 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d259954, d260397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d259954, d260397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d259955 q = 1) (hb : d260398 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d259955, d260398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d259955, d260398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d259957 q = 1) (hb : d260402 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d259957, d260402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d259957, d260402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64412 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d254596 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d259958 q = 1) (hb : d260403 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d259958, d260403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d259958, d260403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d259959 q = 1) (hb : d260404 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d259959, d260404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d259959, d260404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d259960 q = 1) (hb : d260405 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d259960, d260405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d259960, d260405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d259961 q = 1) (hb : d260406 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d259961, d260406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d259961, d260406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d259968 q = 1) (hb : d260412 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d259968, d260412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d259968, d260412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64413 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d254759 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d259969 q = 1) (hb : d260413 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d259969, d260413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d259969, d260413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d259970 q = 1) (hb : d260414 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d259970, d260414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d259970, d260414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d259971 q = 1) (hb : d260415 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d259971, d260415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d259971, d260415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d259972 q = 1) (hb : d260416 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d259972, d260416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d259972, d260416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d259973 q = 1) (hb : d260417 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d259973, d260417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d259973, d260417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro64415 (p : Pattern) (ha : d259979 p = 1) (hb : d260423 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d259974 q = 1) (hb : d260418 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d259974, d260418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d259974, d260418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64414 q ha hb
  have h2 (q : Pattern) (ha : d259975 q = 1) (hb : d260419 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d259975, d260419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d259975, d260419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d259976 q = 1) (hb : d260420 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d259976, d260420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d259976, d260420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d259977 q = 1) (hb : d260421 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d259977, d260421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d259977, d260421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d259978 q = 1) (hb : d260422 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d259978, d260422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d259978, d260422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d259979 q = 1) (hb : d260423 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d259979, d260423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d259979, d260423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro64416 (p : Pattern) (ha : d258152 p = 1) (hb : d260431 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d254876 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d254885 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d254923 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d258147 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d258148 q = 1) (hb : d260427 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d258148, d260427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d258148, d260427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d255011 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d258149 q = 1) (hb : d260428 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d258149, d260428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d258149, d260428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d258150 q = 1) (hb : d260429 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d258150, d260429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d258150, d260429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d258151 q = 1) (hb : d260430 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d258151, d260430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d258151, d260430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d258152 q = 1) (hb : d260431 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d258152, d260431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d258152, d260431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro64417 (p : Pattern) (ha : d258162 p = 1) (hb : d260436 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d254876 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d254885 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d254923 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d258147 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d258148 q = 1) (hb : d260427 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d258148, d260427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d258148, d260427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d255011 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d258149 q = 1) (hb : d260428 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d258149, d260428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d258149, d260428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d258150 q = 1) (hb : d260429 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d258150, d260429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d258150, d260429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d258151 q = 1) (hb : d260430 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d258151, d260430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d258151, d260430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d255021 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d255026 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d255028 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d258157 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d258158 q = 1) (hb : d260432 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d258158, d260432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d258158, d260432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d255035 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d258159 q = 1) (hb : d260433 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d258159, d260433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d258159, d260433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d258160 q = 1) (hb : d260434 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d258160, d260434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d258160, d260434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d258161 q = 1) (hb : d260435 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d258161, d260435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d258161, d260435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d258162 q = 1) (hb : d260436 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d258162, d260436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d258162, d260436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro64418 (p : Pattern) (ha : d259985 p = 1) (hb : d260443 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d255028 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d258157 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d258158 q = 1) (hb : d260432 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d258158, d260432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d258158, d260432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d255035 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d258159 q = 1) (hb : d260433 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d258159, d260433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d258159, d260433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d258160 q = 1) (hb : d260441 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d258160, d260441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d258160, d260441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d258161 q = 1) (hb : d260442 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d258161, d260442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d258161, d260442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d259985 q = 1) (hb : d260443 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d259985, d260443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d259985, d260443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro64419 (p : Pattern) (ha : d259996 p = 1) (hb : d260453 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d255146 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d259991 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d259992 q = 1) (hb : d260449 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d259992, d260449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d259992, d260449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d255205 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d259993 q = 1) (hb : d260450 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d259993, d260450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d259993, d260450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d259994 q = 1) (hb : d260451 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d259994, d260451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d259994, d260451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d259995 q = 1) (hb : d260452 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d259995, d260452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d259995, d260452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d259996 q = 1) (hb : d260453 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d259996, d260453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d259996, d260453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro64420 (p : Pattern) (ha : d260002 p = 1) (hb : d260459 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d254868 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d258163 q = 1) (hb : d260437 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d258163, d260437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64416 q ha hb
    | true =>
      simp only [d258163, d260437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64417 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d255053 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d258164 q = 1) (hb : d260438 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d258164, d260438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d258164, d260438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d259983 q = 1) (hb : d260439 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d259983, d260439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d259983, d260439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d259984 q = 1) (hb : d260440 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d259984, d260440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d259984, d260440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d259986 q = 1) (hb : d260444 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d259986, d260444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d259986, d260444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64418 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d255062 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d259987 q = 1) (hb : d260445 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d259987, d260445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d259987, d260445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d259988 q = 1) (hb : d260446 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d259988, d260446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d259988, d260446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d259989 q = 1) (hb : d260447 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d259989, d260447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d259989, d260447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d259990 q = 1) (hb : d260448 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d259990, d260448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d259990, d260448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d259997 q = 1) (hb : d260454 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d259997, d260454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d259997, d260454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64419 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d255221 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d259998 q = 1) (hb : d260455 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d259998, d260455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d259998, d260455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d259999 q = 1) (hb : d260456 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d259999, d260456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d259999, d260456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d260000 q = 1) (hb : d260457 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d260000, d260457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d260000, d260457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d260001 q = 1) (hb : d260458 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d260001, d260458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d260001, d260458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d260002 q = 1) (hb : d260459 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d260002, d260459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d260002, d260459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro64421 (p : Pattern) (ha : d260008 p = 1) (hb : d260465 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d260003 q = 1) (hb : d260460 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d260003, d260460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d260003, d260460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64420 q ha hb
  have h2 (q : Pattern) (ha : d260004 q = 1) (hb : d260461 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d260004, d260461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d260004, d260461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d260005 q = 1) (hb : d260462 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d260005, d260462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d260005, d260462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d260006 q = 1) (hb : d260463 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d260006, d260463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d260006, d260463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d260007 q = 1) (hb : d260464 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d260007, d260464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d260007, d260464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d260008 q = 1) (hb : d260465 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d260008, d260465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d260008, d260465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro64422 (p : Pattern) (ha : d258445 p = 1) (hb : d260474 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d255310 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d255319 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d255333 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d258440 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d258441 q = 1) (hb : d260470 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d258441, d260470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d258441, d260470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d255388 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d258442 q = 1) (hb : d260471 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d258442, d260471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d258442, d260471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d258443 q = 1) (hb : d260472 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d258443, d260472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d258443, d260472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d258444 q = 1) (hb : d260473 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d258444, d260473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d258444, d260473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d258445 q = 1) (hb : d260474 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d258445, d260474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d258445, d260474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro64423 (p : Pattern) (ha : d258455 p = 1) (hb : d260479 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d255310 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d255319 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d255333 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d258440 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d258441 q = 1) (hb : d260470 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d258441, d260470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d258441, d260470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d255388 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d258442 q = 1) (hb : d260471 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d258442, d260471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d258442, d260471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d258443 q = 1) (hb : d260472 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d258443, d260472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d258443, d260472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d258444 q = 1) (hb : d260473 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d258444, d260473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d258444, d260473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d255398 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d255403 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d255405 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d258450 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d258451 q = 1) (hb : d260475 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d258451, d260475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d258451, d260475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d255412 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d258452 q = 1) (hb : d260476 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d258452, d260476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d258452, d260476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d258453 q = 1) (hb : d260477 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d258453, d260477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d258453, d260477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d258454 q = 1) (hb : d260478 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d258454, d260478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d258454, d260478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d258455 q = 1) (hb : d260479 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d258455, d260479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d258455, d260479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro64424 (p : Pattern) (ha : d260015 p = 1) (hb : d260486 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d255405 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d258450 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d258451 q = 1) (hb : d260475 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d258451, d260475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d258451, d260475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d255412 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d258452 q = 1) (hb : d260476 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d258452, d260476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d258452, d260476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d258453 q = 1) (hb : d260484 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d258453, d260484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d258453, d260484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d258454 q = 1) (hb : d260485 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d258454, d260485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d258454, d260485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d260015 q = 1) (hb : d260486 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d260015, d260486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d260015, d260486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro64425 (p : Pattern) (ha : d260026 p = 1) (hb : d260496 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d255491 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d260021 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d260022 q = 1) (hb : d260492 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d260022, d260492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d260022, d260492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d255537 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d260023 q = 1) (hb : d260493 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d260023, d260493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d260023, d260493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d260024 q = 1) (hb : d260494 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d260024, d260494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d260024, d260494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d260025 q = 1) (hb : d260495 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d260025, d260495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d260025, d260495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d260026 q = 1) (hb : d260496 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d260026, d260496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d260026, d260496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro64426 (p : Pattern) (ha : d260032 p = 1) (hb : d260502 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d255302 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d258456 q = 1) (hb : d260480 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d258456, d260480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64422 q ha hb
    | true =>
      simp only [d258456, d260480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64423 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d255430 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d258457 q = 1) (hb : d260481 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d258457, d260481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d258457, d260481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d260013 q = 1) (hb : d260482 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d260013, d260482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d260013, d260482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d260014 q = 1) (hb : d260483 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d260014, d260483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d260014, d260483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d260016 q = 1) (hb : d260487 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d260016, d260487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d260016, d260487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64424 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d255439 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d260017 q = 1) (hb : d260488 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d260017, d260488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d260017, d260488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d260018 q = 1) (hb : d260489 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d260018, d260489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d260018, d260489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d260019 q = 1) (hb : d260490 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d260019, d260490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d260019, d260490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d260020 q = 1) (hb : d260491 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d260020, d260491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d260020, d260491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d260027 q = 1) (hb : d260497 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d260027, d260497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d260027, d260497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64425 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d255553 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d260028 q = 1) (hb : d260498 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d260028, d260498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d260028, d260498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d260029 q = 1) (hb : d260499 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d260029, d260499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d260029, d260499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d260030 q = 1) (hb : d260500 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d260030, d260500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d260030, d260500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d260031 q = 1) (hb : d260501 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d260031, d260501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d260031, d260501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d260032 q = 1) (hb : d260502 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d260032, d260502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d260032, d260502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro64427 (p : Pattern) (ha : d260038 p = 1) (hb : d260508 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d260033 q = 1) (hb : d260503 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d260033, d260503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d260033, d260503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64426 q ha hb
  have h2 (q : Pattern) (ha : d260034 q = 1) (hb : d260504 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d260034, d260504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d260034, d260504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d260035 q = 1) (hb : d260505 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d260035, d260505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d260035, d260505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d260036 q = 1) (hb : d260506 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d260036, d260506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d260036, d260506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d260037 q = 1) (hb : d260507 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d260037, d260507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d260037, d260507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d260038 q = 1) (hb : d260508 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d260038, d260508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d260038, d260508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro64428 (p : Pattern) (ha : d260044 p = 1) (hb : d260514 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d259925 q = 1) (hb : d260343 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d259925, d260343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64397 q ha hb
    | true =>
      simp only [d259925, d260343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64403 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d259952 q = 1) (hb : d260383 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d259952, d260383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d259952, d260383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64409 q ha hb
  have h3 (q : Pattern) (ha : d259953 q = 1) (hb : d260384 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d259953, d260384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d259953, d260384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d259980 q = 1) (hb : d260424 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d259980, d260424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d259980, d260424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64415 q ha hb
  have h5 (q : Pattern) (ha : d259981 q = 1) (hb : d260425 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d259981, d260425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d259981, d260425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d259982 q = 1) (hb : d260426 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d259982, d260426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d259982, d260426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d260009 q = 1) (hb : d260466 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d260009, d260466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d260009, d260466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64421 q ha hb
  have h8 (q : Pattern) (ha : d260010 q = 1) (hb : d260467 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d260010, d260467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d260010, d260467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d260011 q = 1) (hb : d260468 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d260011, d260468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d260011, d260468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d260012 q = 1) (hb : d260469 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d260012, d260469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d260012, d260469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d260039 q = 1) (hb : d260509 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d260039, d260509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d260039, d260509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64427 q ha hb
  have h12 (q : Pattern) (ha : d260040 q = 1) (hb : d260510 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d260040, d260510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d260040, d260510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d260041 q = 1) (hb : d260511 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d260041, d260511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d260041, d260511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d260042 q = 1) (hb : d260512 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d260042, d260512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d260042, d260512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d260043 q = 1) (hb : d260513 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d260043, d260513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d260043, d260513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d260044 q = 1) (hb : d260514 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d260044, d260514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d260044, d260514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro64429 (p : Pattern) (ha : d260050 p = 1) (hb : d260520 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d260045 q = 1) (hb : d260515 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d260045, d260515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64428 q ha hb
    | true =>
      simp only [d260045, d260515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d260046 q = 1) (hb : d260516 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d260046, d260516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d260046, d260516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d260047 q = 1) (hb : d260517 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d260047, d260517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d260047, d260517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d260048 q = 1) (hb : d260518 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d260048, d260518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d260048, d260518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d260049 q = 1) (hb : d260519 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d260049, d260519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d260049, d260519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d260050 q = 1) (hb : d260520 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d260050, d260520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d260050, d260520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro64430 (p : Pattern) (ha : d260056 p = 1) (hb : d260526 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d260051 q = 1) (hb : d260521 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d260051, d260521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64429 q ha hb
    | true =>
      simp only [d260051, d260521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d260052 q = 1) (hb : d260522 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d260052, d260522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d260052, d260522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d260053 q = 1) (hb : d260523 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d260053, d260523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d260053, d260523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d260054 q = 1) (hb : d260524 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d260054, d260524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d260054, d260524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d260055 q = 1) (hb : d260525 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d260055, d260525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d260055, d260525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d260056 q = 1) (hb : d260526 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d260056, d260526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d260056, d260526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro64431 (p : Pattern) (ha : d260062 p = 1) (hb : d260532 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d260057 q = 1) (hb : d260527 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d260057, d260527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64430 q ha hb
    | true =>
      simp only [d260057, d260527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d260058 q = 1) (hb : d260528 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d260058, d260528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d260058, d260528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d260059 q = 1) (hb : d260529 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d260059, d260529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d260059, d260529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d260060 q = 1) (hb : d260530 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d260060, d260530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d260060, d260530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d260061 q = 1) (hb : d260531 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d260061, d260531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d260061, d260531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d260062 q = 1) (hb : d260532 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d260062, d260532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d260062, d260532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro64432 (p : Pattern) (ha : d260068 p = 1) (hb : d260538 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d260063 q = 1) (hb : d260533 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d260063, d260533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64431 q ha hb
    | true =>
      simp only [d260063, d260533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d260064 q = 1) (hb : d260534 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d260064, d260534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d260064, d260534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d260065 q = 1) (hb : d260535 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d260065, d260535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d260065, d260535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d260066 q = 1) (hb : d260536 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d260066, d260536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d260066, d260536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d260067 q = 1) (hb : d260537 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d260067, d260537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d260067, d260537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d260068 q = 1) (hb : d260538 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d260068, d260538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d260068, d260538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro64433 (p : Pattern) (ha : d260074 p = 1) (hb : d260544 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d260069 q = 1) (hb : d260539 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d260069, d260539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64432 q ha hb
    | true =>
      simp only [d260069, d260539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d260070 q = 1) (hb : d260540 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d260070, d260540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d260070, d260540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d260071 q = 1) (hb : d260541 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d260071, d260541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d260071, d260541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d260072 q = 1) (hb : d260542 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d260072, d260542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d260072, d260542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d260073 q = 1) (hb : d260543 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d260073, d260543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d260073, d260543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d260074 q = 1) (hb : d260544 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d260074, d260544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d260074, d260544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro64434 (p : Pattern) (ha : d260080 p = 1) (hb : d260550 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d260075 q = 1) (hb : d260545 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d260075, d260545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64433 q ha hb
    | true =>
      simp only [d260075, d260545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d260076 q = 1) (hb : d260546 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d260076, d260546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d260076, d260546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d260077 q = 1) (hb : d260547 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d260077, d260547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d260077, d260547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d260078 q = 1) (hb : d260548 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d260078, d260548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d260078, d260548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d260079 q = 1) (hb : d260549 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d260079, d260549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d260079, d260549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d260080 q = 1) (hb : d260550 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d260080, d260550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d260080, d260550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro64435 (p : Pattern) (ha : d260086 p = 1) (hb : d260556 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d260081 q = 1) (hb : d260551 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d260081, d260551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64434 q ha hb
    | true =>
      simp only [d260081, d260551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d260082 q = 1) (hb : d260552 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d260082, d260552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d260082, d260552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d260083 q = 1) (hb : d260553 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d260083, d260553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d260083, d260553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d260084 q = 1) (hb : d260554 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d260084, d260554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d260084, d260554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d260085 q = 1) (hb : d260555 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d260085, d260555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d260085, d260555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d260086 q = 1) (hb : d260556 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d260086, d260556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d260086, d260556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro64436 (p : Pattern) (ha : d25104 p = 1) (hb : d208034 p = 1) : d25221 p = 1 := by
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
  have h5 (q : Pattern) (ha : d23 q = 1) (hb : d208034 q = 1) : d23 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d25104 q = 1) (hb : d208034 q = 1) : d25221 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d25104, d25221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25104, d25221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro64437 (p : Pattern) (ha : d25110 p = 1) (hb : d208034 p = 1) : d25461 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25105 q = 1) (hb : d208034 q = 1) : d25222 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25105, d25222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64436 q ha hb
    | true =>
      simp only [d25105, d25222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25106 q = 1) (hb : d208034 q = 1) : d25223 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25106, d25223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d25106, d25223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d25107 q = 1) (hb : d208034 q = 1) : d25224 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d25107, d25224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25107, d25224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d25108 q = 1) (hb : d208034 q = 1) : d25225 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d25108, d25225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25108, d25225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d28 q = 1) (hb : d208034 q = 1) : d28 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d25109 q = 1) (hb : d208034 q = 1) : d25226 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d25109, d25226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25109, d25226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d29 q = 1) (hb : d208034 q = 1) : d29 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d25110 q = 1) (hb : d208034 q = 1) : d25461 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d25110, d25461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25110, d25461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro64438 (p : Pattern) (ha : d25116 p = 1) (hb : d208034 p = 1) : d240217 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30 q = 1) (hb : d208034 q = 1) : d30 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d25111 q = 1) (hb : d208034 q = 1) : d240212 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d25111, d240212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64437 q ha hb
    | true =>
      simp only [d25111, d240212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25112 q = 1) (hb : d208034 q = 1) : d240213 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d25112, d240213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25112, d240213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d25113 q = 1) (hb : d208034 q = 1) : d240214 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d25113, d240214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25113, d240214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33 q = 1) (hb : d208034 q = 1) : d33 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d25114 q = 1) (hb : d208034 q = 1) : d240215 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d25114, d240215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25114, d240215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d34 q = 1) (hb : d208034 q = 1) : d34 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d25115 q = 1) (hb : d208034 q = 1) : d240216 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d25115, d240216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25115, d240216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d25116 q = 1) (hb : d208034 q = 1) : d240217 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d25116, d240217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d25116, d240217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h9 p ha hb
theorem andIntro64439 (p : Pattern) (ha : d25122 p = 1) (hb : d208034 p = 1) : d240223 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25117 q = 1) (hb : d208034 q = 1) : d240218 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25117, d240218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64438 q ha hb
    | true =>
      simp only [d25117, d240218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25118 q = 1) (hb : d208034 q = 1) : d240219 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25118, d240219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25118, d240219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d208034 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d25119 q = 1) (hb : d208034 q = 1) : d240220 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25119, d240220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25119, d240220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25120 q = 1) (hb : d208034 q = 1) : d240221 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25120, d240221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25120, d240221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d25121 q = 1) (hb : d208034 q = 1) : d240222 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25121, d240222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25121, d240222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25122 q = 1) (hb : d208034 q = 1) : d240223 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25122, d240223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25122, d240223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro64440 (p : Pattern) (ha : d201977 p = 1) (hb : d208034 p = 1) : d240229 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d120 q = 1) (hb : d208034 q = 1) : d120 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d126 q = 1) (hb : d208034 q = 1) : d126 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d42 q = 1) (hb : d208034 q = 1) : d42 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d25123 q = 1) (hb : d208034 q = 1) : d240224 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25123, d240224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64439 q ha hb
    | true =>
      simp only [d25123, d240224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d201973 q = 1) (hb : d208034 q = 1) : d240225 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d201973, d240225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d201973, d240225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d44 q = 1) (hb : d208034 q = 1) : d44 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d201974 q = 1) (hb : d208034 q = 1) : d240226 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d201974, d240226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d201974, d240226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d201975 q = 1) (hb : d208034 q = 1) : d240227 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d201975, d240227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d201975, d240227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d201976 q = 1) (hb : d208034 q = 1) : d240228 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d201976, d240228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d201976, d240228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d201977 q = 1) (hb : d208034 q = 1) : d240229 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d201977, d240229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d201977, d240229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro64441 (p : Pattern) (ha : d25129 p = 1) (hb : d208034 p = 1) : d240230 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25117 q = 1) (hb : d208034 q = 1) : d240218 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25117, d240218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64438 q ha hb
    | true =>
      simp only [d25117, d240218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25118 q = 1) (hb : d208034 q = 1) : d240219 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25118, d240219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25118, d240219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d208034 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d25119 q = 1) (hb : d208034 q = 1) : d240220 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25119, d240220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25119, d240220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25120 q = 1) (hb : d208034 q = 1) : d240221 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25120, d240221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25120, d240221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d25121 q = 1) (hb : d208034 q = 1) : d240222 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25121, d240222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25121, d240222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25129 q = 1) (hb : d208034 q = 1) : d240230 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25129, d240230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25129, d240230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro64442 (p : Pattern) (ha : d201982 p = 1) (hb : d208034 p = 1) : d240236 p = 1 := by
  have h0 (q : Pattern) (ha : d120 q = 1) (hb : d208034 q = 1) : d120 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d126 q = 1) (hb : d208034 q = 1) : d126 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d42 q = 1) (hb : d208034 q = 1) : d42 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d25123 q = 1) (hb : d208034 q = 1) : d240224 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25123, d240224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64439 q ha hb
    | true =>
      simp only [d25123, d240224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d201973 q = 1) (hb : d208034 q = 1) : d240225 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d201973, d240225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d201973, d240225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44 q = 1) (hb : d208034 q = 1) : d44 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d201974 q = 1) (hb : d208034 q = 1) : d240226 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d201974, d240226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d201974, d240226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d201975 q = 1) (hb : d208034 q = 1) : d240227 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d201975, d240227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d201975, d240227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d201976 q = 1) (hb : d208034 q = 1) : d240228 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d201976, d240228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d201976, d240228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d198 q = 1) (hb : d208034 q = 1) : d198 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d202 q = 1) (hb : d208034 q = 1) : d202 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d49 q = 1) (hb : d208034 q = 1) : d49 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d25130 q = 1) (hb : d208034 q = 1) : d240231 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25130, d240231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64441 q ha hb
    | true =>
      simp only [d25130, d240231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d201978 q = 1) (hb : d208034 q = 1) : d240232 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d201978, d240232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d201978, d240232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h15 (q : Pattern) (ha : d51 q = 1) (hb : d208034 q = 1) : d51 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d201979 q = 1) (hb : d208034 q = 1) : d240233 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d201979, d240233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d201979, d240233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d201980 q = 1) (hb : d208034 q = 1) : d240234 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d201980, d240234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d201980, d240234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d201981 q = 1) (hb : d208034 q = 1) : d240235 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d201981, d240235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d201981, d240235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d201982 q = 1) (hb : d208034 q = 1) : d240236 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d201982, d240236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d201982, d240236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro64443 (p : Pattern) (ha : d201989 p = 1) (hb : d208034 p = 1) : d240243 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d49 q = 1) (hb : d208034 q = 1) : d49 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d25130 q = 1) (hb : d208034 q = 1) : d240231 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25130, d240231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64441 q ha hb
    | true =>
      simp only [d25130, d240231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d201978 q = 1) (hb : d208034 q = 1) : d240232 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d201978, d240232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d201978, d240232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d51 q = 1) (hb : d208034 q = 1) : d51 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d201979 q = 1) (hb : d208034 q = 1) : d240233 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d201979, d240233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d201979, d240233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d201987 q = 1) (hb : d208034 q = 1) : d240241 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d201987, d240241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d201987, d240241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d201988 q = 1) (hb : d208034 q = 1) : d240242 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d201988, d240242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d201988, d240242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d201989 q = 1) (hb : d208034 q = 1) : d240243 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d201989, d240243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d201989, d240243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro64444 (p : Pattern) (ha : d25153 p = 1) (hb : d208034 p = 1) : d25595 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25148 q = 1) (hb : d208034 q = 1) : d25314 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25148, d25314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25148, d25314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64436 q ha hb
  have h2 (q : Pattern) (ha : d25105 q = 1) (hb : d208034 q = 1) : d25222 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25105, d25222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64436 q ha hb
    | true =>
      simp only [d25105, d25222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d25149 q = 1) (hb : d208034 q = 1) : d25315 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25149, d25315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d25149, d25315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d25106 q = 1) (hb : d208034 q = 1) : d25223 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25106, d25223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25106, d25223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25150 q = 1) (hb : d208034 q = 1) : d25316 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d25150, d25316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25150, d25316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25151 q = 1) (hb : d208034 q = 1) : d25317 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d25151, d25317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25151, d25317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d69 q = 1) (hb : d208034 q = 1) : d69 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d25152 q = 1) (hb : d208034 q = 1) : d25318 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d25152, d25318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25152, d25318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d70 q = 1) (hb : d208034 q = 1) : d70 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d25153 q = 1) (hb : d208034 q = 1) : d25595 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d25153, d25595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d25153, d25595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro64445 (p : Pattern) (ha : d25159 p = 1) (hb : d208034 p = 1) : d240254 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d71 q = 1) (hb : d208034 q = 1) : d71 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d25154 q = 1) (hb : d208034 q = 1) : d240249 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d25154, d240249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64444 q ha hb
    | true =>
      simp only [d25154, d240249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25155 q = 1) (hb : d208034 q = 1) : d240250 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d25155, d240250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25155, d240250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d25156 q = 1) (hb : d208034 q = 1) : d240251 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d25156, d240251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25156, d240251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d74 q = 1) (hb : d208034 q = 1) : d74 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d25157 q = 1) (hb : d208034 q = 1) : d240252 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d25157, d240252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25157, d240252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d75 q = 1) (hb : d208034 q = 1) : d75 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d25158 q = 1) (hb : d208034 q = 1) : d240253 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d25158, d240253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25158, d240253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d25159 q = 1) (hb : d208034 q = 1) : d240254 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d25159, d240254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d25159, d240254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h9 p ha hb
theorem andIntro64446 (p : Pattern) (ha : d25165 p = 1) (hb : d208034 p = 1) : d240260 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25160 q = 1) (hb : d208034 q = 1) : d240255 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25160, d240255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64445 q ha hb
    | true =>
      simp only [d25160, d240255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25161 q = 1) (hb : d208034 q = 1) : d240256 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25161, d240256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25161, d240256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d79 q = 1) (hb : d208034 q = 1) : d79 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d25162 q = 1) (hb : d208034 q = 1) : d240257 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25162, d240257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25162, d240257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25163 q = 1) (hb : d208034 q = 1) : d240258 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25163, d240258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25163, d240258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d25164 q = 1) (hb : d208034 q = 1) : d240259 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25164, d240259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25164, d240259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25165 q = 1) (hb : d208034 q = 1) : d240260 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25165, d240260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25165, d240260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro64447 (p : Pattern) (ha : d201999 p = 1) (hb : d208034 p = 1) : d240266 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83 q = 1) (hb : d208034 q = 1) : d83 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d25166 q = 1) (hb : d208034 q = 1) : d240261 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25166, d240261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64446 q ha hb
    | true =>
      simp only [d25166, d240261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d201995 q = 1) (hb : d208034 q = 1) : d240262 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d201995, d240262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d201995, d240262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d85 q = 1) (hb : d208034 q = 1) : d85 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d201996 q = 1) (hb : d208034 q = 1) : d240263 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d201996, d240263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d201996, d240263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d201997 q = 1) (hb : d208034 q = 1) : d240264 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d201997, d240264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d201997, d240264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d201998 q = 1) (hb : d208034 q = 1) : d240265 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d201998, d240265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d201998, d240265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d201999 q = 1) (hb : d208034 q = 1) : d240266 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d201999, d240266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d201999, d240266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro64448 (p : Pattern) (ha : d202005 p = 1) (hb : d208034 p = 1) : d240272 p = 1 := by
  have h0 (q : Pattern) (ha : d114 q = 1) (hb : d208034 q = 1) : d114 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d201983 q = 1) (hb : d208034 q = 1) : d240237 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d201983, d240237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64440 q ha hb
    | true =>
      simp only [d201983, d240237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64442 q ha hb
  have h2 (q : Pattern) (ha : d214 q = 1) (hb : d208034 q = 1) : d214 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d201984 q = 1) (hb : d208034 q = 1) : d240238 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d201984, d240238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d201984, d240238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d201985 q = 1) (hb : d208034 q = 1) : d240239 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d201985, d240239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d201985, d240239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d201986 q = 1) (hb : d208034 q = 1) : d240240 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d201986, d240240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d201986, d240240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d201990 q = 1) (hb : d208034 q = 1) : d240244 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d201990, d240244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d201990, d240244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64443 q ha hb
  have h8 (q : Pattern) (ha : d201991 q = 1) (hb : d208034 q = 1) : d240245 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d201991, d240245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d201991, d240245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h9 (q : Pattern) (ha : d201992 q = 1) (hb : d208034 q = 1) : d240246 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d201992, d240246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d201992, d240246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d201993 q = 1) (hb : d208034 q = 1) : d240247 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d201993, d240247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d201993, d240247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d201994 q = 1) (hb : d208034 q = 1) : d240248 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d201994, d240248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d201994, d240248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d202000 q = 1) (hb : d208034 q = 1) : d240267 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d202000, d240267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d202000, d240267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64447 q ha hb
  have h13 (q : Pattern) (ha : d202001 q = 1) (hb : d208034 q = 1) : d240268 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d202001, d240268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d202001, d240268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h14 (q : Pattern) (ha : d202002 q = 1) (hb : d208034 q = 1) : d240269 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d202002, d240269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d202002, d240269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h15 (q : Pattern) (ha : d202003 q = 1) (hb : d208034 q = 1) : d240270 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d202003, d240270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d202003, d240270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h16 (q : Pattern) (ha : d202004 q = 1) (hb : d208034 q = 1) : d240271 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d202004, d240271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d202004, d240271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d202005 q = 1) (hb : d208034 q = 1) : d240272 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d202005, d240272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d202005, d240272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro64449 (p : Pattern) (ha : d25187 p = 1) (hb : d208034 p = 1) : d240282 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42 q = 1) (hb : d208034 q = 1) : d42 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d25123 q = 1) (hb : d208034 q = 1) : d240224 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25123, d240224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64439 q ha hb
    | true =>
      simp only [d25123, d240224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25183 q = 1) (hb : d208034 q = 1) : d240278 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25183, d240278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25183, d240278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d25184 q = 1) (hb : d208034 q = 1) : d240279 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25184, d240279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25184, d240279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25185 q = 1) (hb : d208034 q = 1) : d240280 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25185, d240280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25185, d240280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25186 q = 1) (hb : d208034 q = 1) : d240281 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d25186, d240281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25186, d240281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d25187 q = 1) (hb : d208034 q = 1) : d240282 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d25187, d240282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25187, d240282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro64450 (p : Pattern) (ha : d25194 p = 1) (hb : d208034 p = 1) : d240289 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42 q = 1) (hb : d208034 q = 1) : d42 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d25123 q = 1) (hb : d208034 q = 1) : d240224 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25123, d240224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64439 q ha hb
    | true =>
      simp only [d25123, d240224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25183 q = 1) (hb : d208034 q = 1) : d240278 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25183, d240278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25183, d240278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d25184 q = 1) (hb : d208034 q = 1) : d240279 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25184, d240279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25184, d240279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25185 q = 1) (hb : d208034 q = 1) : d240280 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25185, d240280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25185, d240280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25186 q = 1) (hb : d208034 q = 1) : d240281 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d25186, d240281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25186, d240281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d49 q = 1) (hb : d208034 q = 1) : d49 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d25130 q = 1) (hb : d208034 q = 1) : d240231 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25130, d240231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64441 q ha hb
    | true =>
      simp only [d25130, d240231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d25190 q = 1) (hb : d208034 q = 1) : d240285 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25190, d240285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25190, d240285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d25191 q = 1) (hb : d208034 q = 1) : d240286 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25191, d240286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d25191, d240286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d25192 q = 1) (hb : d208034 q = 1) : d240287 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25192, d240287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25192, d240287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d25193 q = 1) (hb : d208034 q = 1) : d240288 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d25193, d240288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25193, d240288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d25194 q = 1) (hb : d208034 q = 1) : d240289 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d25194, d240289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25194, d240289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro64451 (p : Pattern) (ha : d25296 p = 1) (hb : d208034 p = 1) : d240350 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42 q = 1) (hb : d208034 q = 1) : d42 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d25123 q = 1) (hb : d208034 q = 1) : d240224 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25123, d240224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64439 q ha hb
    | true =>
      simp only [d25123, d240224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25183 q = 1) (hb : d208034 q = 1) : d240278 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25183, d240278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25183, d240278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d25184 q = 1) (hb : d208034 q = 1) : d240279 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25184, d240279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25184, d240279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25185 q = 1) (hb : d208034 q = 1) : d240280 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25185, d240280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25185, d240280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25186 q = 1) (hb : d208034 q = 1) : d240281 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d25186, d240281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25186, d240281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d103 q = 1) (hb : d208034 q = 1) : d103 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d25296 q = 1) (hb : d208034 q = 1) : d240350 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d25296, d240350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25296, d240350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro64452 (p : Pattern) (ha : d25199 p = 1) (hb : d208034 p = 1) : d240294 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25117 q = 1) (hb : d208034 q = 1) : d240218 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25117, d240218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64438 q ha hb
    | true =>
      simp only [d25117, d240218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25118 q = 1) (hb : d208034 q = 1) : d240219 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25118, d240219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25118, d240219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d208034 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d25119 q = 1) (hb : d208034 q = 1) : d240220 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25119, d240220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25119, d240220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25120 q = 1) (hb : d208034 q = 1) : d240221 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25120, d240221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25120, d240221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d25198 q = 1) (hb : d208034 q = 1) : d240293 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25198, d240293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25198, d240293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d25199 q = 1) (hb : d208034 q = 1) : d240294 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25199, d240294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25199, d240294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro64453 (p : Pattern) (ha : d25206 p = 1) (hb : d208034 p = 1) : d240301 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25117 q = 1) (hb : d208034 q = 1) : d240218 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25117, d240218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64438 q ha hb
    | true =>
      simp only [d25117, d240218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25118 q = 1) (hb : d208034 q = 1) : d240219 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25118, d240219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25118, d240219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d208034 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d25119 q = 1) (hb : d208034 q = 1) : d240220 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25119, d240220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25119, d240220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25204 q = 1) (hb : d208034 q = 1) : d240299 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25204, d240299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25204, d240299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25205 q = 1) (hb : d208034 q = 1) : d240300 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25205, d240300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25205, d240300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25206 q = 1) (hb : d208034 q = 1) : d240301 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25206, d240301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25206, d240301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro64454 (p : Pattern) (ha : d25213 p = 1) (hb : d208034 p = 1) : d25451 p = 1 := by
  have h0 (q : Pattern) (ha : d25210 q = 1) (hb : d152852 q = 1) : d25210 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d9796 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d25211 q = 1) (hb : d208034 q = 1) : d25449 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d25211, d208034, d25449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25211, d208034, d25449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d25212 q = 1) (hb : d208034 q = 1) : d25450 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d25212, d25450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25212, d25450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9796 q = 1) (hb : d152852 q = 1) : d9796 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d21 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d25102 q = 1) (hb : d208034 q = 1) : d25219 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d25102, d208034, d25219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25102, d208034, d25219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d25103 q = 1) (hb : d208034 q = 1) : d25220 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d25103, d25220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25103, d25220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h9 (q : Pattern) (ha : d25213 q = 1) (hb : d208034 q = 1) : d25451 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d25213, d25451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25213, d25451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro64455 (p : Pattern) (ha : d25227 p = 1) (hb : d208034 p = 1) : d240305 p = 1 := by
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
  have h5 (q : Pattern) (ha : d25105 q = 1) (hb : d208034 q = 1) : d25222 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25105, d25222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64436 q ha hb
    | true =>
      simp only [d25105, d25222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d25106 q = 1) (hb : d208034 q = 1) : d25223 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25106, d25223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25106, d25223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25107 q = 1) (hb : d208034 q = 1) : d25224 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d25107, d25224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25107, d25224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d25108 q = 1) (hb : d208034 q = 1) : d25225 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d25108, d25225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25108, d25225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d25218 q = 1) (hb : d208034 q = 1) : d25456 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d25218, d25456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25218, d25456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d25226 q = 1) (hb : d208034 q = 1) : d25226 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d25227 q = 1) (hb : d208034 q = 1) : d240305 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d25227, d240305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d25227, d240305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro64456 (p : Pattern) (ha : d25233 p = 1) (hb : d208034 p = 1) : d240311 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25228 q = 1) (hb : d208034 q = 1) : d240306 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d25228, d240306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64455 q ha hb
    | true =>
      simp only [d25228, d240306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64437 q ha hb
  have h2 (q : Pattern) (ha : d25229 q = 1) (hb : d208034 q = 1) : d240307 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d25229, d240307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25229, d240307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25230 q = 1) (hb : d208034 q = 1) : d240308 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d25230, d240308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25230, d240308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d30 q = 1) (hb : d208034 q = 1) : d30 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d25111 q = 1) (hb : d208034 q = 1) : d240212 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d25111, d240212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64437 q ha hb
    | true =>
      simp only [d25111, d240212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25112 q = 1) (hb : d208034 q = 1) : d240213 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d25112, d240213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25112, d240213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d25113 q = 1) (hb : d208034 q = 1) : d240214 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d25113, d240214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25113, d240214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d25231 q = 1) (hb : d208034 q = 1) : d240309 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d25231, d240309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25231, d240309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d33 q = 1) (hb : d208034 q = 1) : d33 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d25114 q = 1) (hb : d208034 q = 1) : d240215 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d25114, d240215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25114, d240215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d25232 q = 1) (hb : d208034 q = 1) : d240310 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d25232, d240310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d25232, d240310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d25233 q = 1) (hb : d208034 q = 1) : d240311 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d25233, d240311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d25233, d240311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h12 p ha hb
theorem andIntro64457 (p : Pattern) (ha : d25239 p = 1) (hb : d208034 p = 1) : d240317 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25234 q = 1) (hb : d208034 q = 1) : d240312 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25234, d240312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64456 q ha hb
    | true =>
      simp only [d25234, d240312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25235 q = 1) (hb : d208034 q = 1) : d240313 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25235, d240313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25235, d240313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25117 q = 1) (hb : d208034 q = 1) : d240218 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25117, d240218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64438 q ha hb
    | true =>
      simp only [d25117, d240218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25118 q = 1) (hb : d208034 q = 1) : d240219 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25118, d240219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25118, d240219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25236 q = 1) (hb : d208034 q = 1) : d240314 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25236, d240314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25236, d240314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25237 q = 1) (hb : d208034 q = 1) : d240315 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25237, d240315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25237, d240315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25238 q = 1) (hb : d208034 q = 1) : d240316 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25238, d240316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25238, d240316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d25239 q = 1) (hb : d208034 q = 1) : d240317 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25239, d240317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25239, d240317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro64458 (p : Pattern) (ha : d25267 p = 1) (hb : d208034 p = 1) : d240323 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25117 q = 1) (hb : d208034 q = 1) : d240218 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25117, d240218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64438 q ha hb
    | true =>
      simp only [d25117, d240218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25118 q = 1) (hb : d208034 q = 1) : d240219 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25118, d240219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25118, d240219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25264 q = 1) (hb : d208034 q = 1) : d240320 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25264, d240320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25264, d240320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25265 q = 1) (hb : d208034 q = 1) : d240321 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25265, d240321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25265, d240321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25266 q = 1) (hb : d208034 q = 1) : d240322 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25266, d240322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25266, d240322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d25267 q = 1) (hb : d208034 q = 1) : d240323 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25267, d240323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25267, d240323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro64459 (p : Pattern) (ha : d202015 p = 1) (hb : d208034 p = 1) : d240329 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d116 q = 1) (hb : d208034 q = 1) : d116 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d25200 q = 1) (hb : d208034 q = 1) : d240295 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25200, d240295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64452 q ha hb
    | true =>
      simp only [d25200, d240295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25201 q = 1) (hb : d208034 q = 1) : d240296 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25201, d240296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25201, d240296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d25202 q = 1) (hb : d208034 q = 1) : d240297 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25202, d240297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25202, d240297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25203 q = 1) (hb : d208034 q = 1) : d240298 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25203, d240298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25203, d240298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123 q = 1) (hb : d208034 q = 1) : d123 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d25207 q = 1) (hb : d208034 q = 1) : d240302 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25207, d240302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64453 q ha hb
    | true =>
      simp only [d25207, d240302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d25208 q = 1) (hb : d208034 q = 1) : d240303 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25208, d240303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25208, d240303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d25209 q = 1) (hb : d208034 q = 1) : d240304 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25209, d240304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d25209, d240304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d25240 q = 1) (hb : d208034 q = 1) : d240318 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25240, d240318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64457 q ha hb
    | true =>
      simp only [d25240, d240318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64439 q ha hb
  have h11 (q : Pattern) (ha : d202011 q = 1) (hb : d208034 q = 1) : d240319 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202011, d240319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d202011, d240319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d25268 q = 1) (hb : d208034 q = 1) : d240324 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25268, d240324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64458 q ha hb
    | true =>
      simp only [d25268, d240324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d25269 q = 1) (hb : d208034 q = 1) : d240325 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25269, d240325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d25269, d240325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d202012 q = 1) (hb : d208034 q = 1) : d240326 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202012, d240326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d202012, d240326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d202013 q = 1) (hb : d208034 q = 1) : d240327 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202013, d240327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d202013, d240327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d202014 q = 1) (hb : d208034 q = 1) : d240328 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202014, d240328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d202014, d240328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d202015 q = 1) (hb : d208034 q = 1) : d240329 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d202015, d240329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202015, d240329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro64460 (p : Pattern) (ha : d25274 p = 1) (hb : d208034 p = 1) : d240330 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25117 q = 1) (hb : d208034 q = 1) : d240218 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25117, d240218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64438 q ha hb
    | true =>
      simp only [d25117, d240218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25118 q = 1) (hb : d208034 q = 1) : d240219 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25118, d240219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25118, d240219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d208034 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d25119 q = 1) (hb : d208034 q = 1) : d240220 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25119, d240220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25119, d240220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25120 q = 1) (hb : d208034 q = 1) : d240221 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25120, d240221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25120, d240221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d25198 q = 1) (hb : d208034 q = 1) : d240293 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25198, d240293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25198, d240293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d25274 q = 1) (hb : d208034 q = 1) : d240330 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25274, d240330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25274, d240330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro64461 (p : Pattern) (ha : d25279 p = 1) (hb : d208034 p = 1) : d240335 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25117 q = 1) (hb : d208034 q = 1) : d240218 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25117, d240218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64438 q ha hb
    | true =>
      simp only [d25117, d240218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25118 q = 1) (hb : d208034 q = 1) : d240219 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25118, d240219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25118, d240219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d208034 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d25119 q = 1) (hb : d208034 q = 1) : d240220 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25119, d240220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25119, d240220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25204 q = 1) (hb : d208034 q = 1) : d240299 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25204, d240299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25204, d240299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25205 q = 1) (hb : d208034 q = 1) : d240300 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25205, d240300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25205, d240300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25279 q = 1) (hb : d208034 q = 1) : d240335 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25279, d240335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25279, d240335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro64462 (p : Pattern) (ha : d25283 p = 1) (hb : d208034 p = 1) : d240339 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25234 q = 1) (hb : d208034 q = 1) : d240312 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25234, d240312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64456 q ha hb
    | true =>
      simp only [d25234, d240312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25235 q = 1) (hb : d208034 q = 1) : d240313 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25235, d240313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25235, d240313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25117 q = 1) (hb : d208034 q = 1) : d240218 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25117, d240218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64438 q ha hb
    | true =>
      simp only [d25117, d240218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25118 q = 1) (hb : d208034 q = 1) : d240219 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25118, d240219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25118, d240219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25236 q = 1) (hb : d208034 q = 1) : d240314 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25236, d240314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25236, d240314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25237 q = 1) (hb : d208034 q = 1) : d240315 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25237, d240315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25237, d240315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25238 q = 1) (hb : d208034 q = 1) : d240316 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25238, d240316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25238, d240316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d25283 q = 1) (hb : d208034 q = 1) : d240339 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25283, d240339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25283, d240339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro64463 (p : Pattern) (ha : d25288 p = 1) (hb : d208034 p = 1) : d240342 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25117 q = 1) (hb : d208034 q = 1) : d240218 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25117, d240218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64438 q ha hb
    | true =>
      simp only [d25117, d240218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25118 q = 1) (hb : d208034 q = 1) : d240219 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25118, d240219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25118, d240219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25264 q = 1) (hb : d208034 q = 1) : d240320 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25264, d240320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25264, d240320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25265 q = 1) (hb : d208034 q = 1) : d240321 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25265, d240321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25265, d240321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25266 q = 1) (hb : d208034 q = 1) : d240322 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25266, d240322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25266, d240322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d25288 q = 1) (hb : d208034 q = 1) : d240342 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25288, d240342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25288, d240342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro64464 (p : Pattern) (ha : d202020 p = 1) (hb : d208034 p = 1) : d240348 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d116 q = 1) (hb : d208034 q = 1) : d116 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d25200 q = 1) (hb : d208034 q = 1) : d240295 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25200, d240295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64452 q ha hb
    | true =>
      simp only [d25200, d240295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25201 q = 1) (hb : d208034 q = 1) : d240296 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25201, d240296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25201, d240296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d25202 q = 1) (hb : d208034 q = 1) : d240297 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25202, d240297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25202, d240297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25203 q = 1) (hb : d208034 q = 1) : d240298 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25203, d240298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25203, d240298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123 q = 1) (hb : d208034 q = 1) : d123 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d25207 q = 1) (hb : d208034 q = 1) : d240302 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25207, d240302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64453 q ha hb
    | true =>
      simp only [d25207, d240302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d25208 q = 1) (hb : d208034 q = 1) : d240303 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25208, d240303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25208, d240303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d25209 q = 1) (hb : d208034 q = 1) : d240304 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25209, d240304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d25209, d240304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d25240 q = 1) (hb : d208034 q = 1) : d240318 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25240, d240318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64457 q ha hb
    | true =>
      simp only [d25240, d240318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64439 q ha hb
  have h11 (q : Pattern) (ha : d202011 q = 1) (hb : d208034 q = 1) : d240319 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202011, d240319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d202011, d240319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d25268 q = 1) (hb : d208034 q = 1) : d240324 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25268, d240324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64458 q ha hb
    | true =>
      simp only [d25268, d240324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d25269 q = 1) (hb : d208034 q = 1) : d240325 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25269, d240325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d25269, d240325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d202012 q = 1) (hb : d208034 q = 1) : d240326 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202012, d240326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d202012, d240326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d202013 q = 1) (hb : d208034 q = 1) : d240327 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202013, d240327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d202013, d240327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d202014 q = 1) (hb : d208034 q = 1) : d240328 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202014, d240328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d202014, d240328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d194 q = 1) (hb : d208034 q = 1) : d194 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d25275 q = 1) (hb : d208034 q = 1) : d240331 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25275, d240331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64460 q ha hb
    | true =>
      simp only [d25275, d240331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d25276 q = 1) (hb : d208034 q = 1) : d240332 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25276, d240332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25276, d240332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d25277 q = 1) (hb : d208034 q = 1) : d240333 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25277, d240333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d25277, d240333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d25278 q = 1) (hb : d208034 q = 1) : d240334 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25278, d240334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25278, d240334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d199 q = 1) (hb : d208034 q = 1) : d199 q = 1 := by
    exact ha
  have h23 (q : Pattern) (ha : d25280 q = 1) (hb : d208034 q = 1) : d240336 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25280, d240336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64461 q ha hb
    | true =>
      simp only [d25280, d240336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d25281 q = 1) (hb : d208034 q = 1) : d240337 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25281, d240337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25281, d240337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d25282 q = 1) (hb : d208034 q = 1) : d240338 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25282, d240338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d25282, d240338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d25284 q = 1) (hb : d208034 q = 1) : d240340 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25284, d240340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64462 q ha hb
    | true =>
      simp only [d25284, d240340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64441 q ha hb
  have h27 (q : Pattern) (ha : d202016 q = 1) (hb : d208034 q = 1) : d240341 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202016, d240341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d202016, d240341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h28 (q : Pattern) (ha : d25289 q = 1) (hb : d208034 q = 1) : d240343 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25289, d240343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64463 q ha hb
    | true =>
      simp only [d25289, d240343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h29 (q : Pattern) (ha : d25290 q = 1) (hb : d208034 q = 1) : d240344 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25290, d240344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
    | true =>
      simp only [d25290, d240344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h30 (q : Pattern) (ha : d202017 q = 1) (hb : d208034 q = 1) : d240345 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202017, d240345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
    | true =>
      simp only [d202017, d240345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d202018 q = 1) (hb : d208034 q = 1) : d240346 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202018, d240346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d202018, d240346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  have h32 (q : Pattern) (ha : d202019 q = 1) (hb : d208034 q = 1) : d240347 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202019, d240347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d202019, d240347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
  have h33 (q : Pattern) (ha : d202020 q = 1) (hb : d208034 q = 1) : d240348 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d202020, d240348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d202020, d240348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h32 q ha hb
  exact h33 p ha hb
theorem andIntro64465 (p : Pattern) (ha : d202027 p = 1) (hb : d208034 p = 1) : d240357 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25284 q = 1) (hb : d208034 q = 1) : d240340 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25284, d240340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64462 q ha hb
    | true =>
      simp only [d25284, d240340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64441 q ha hb
  have h2 (q : Pattern) (ha : d202016 q = 1) (hb : d208034 q = 1) : d240341 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202016, d240341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d202016, d240341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d25289 q = 1) (hb : d208034 q = 1) : d240343 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25289, d240343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64463 q ha hb
    | true =>
      simp only [d25289, d240343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25290 q = 1) (hb : d208034 q = 1) : d240344 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25290, d240344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25290, d240344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d202017 q = 1) (hb : d208034 q = 1) : d240345 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202017, d240345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d202017, d240345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d202025 q = 1) (hb : d208034 q = 1) : d240355 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202025, d240355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202025, d240355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d202026 q = 1) (hb : d208034 q = 1) : d240356 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202026, d240356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202026, d240356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d202027 q = 1) (hb : d208034 q = 1) : d240357 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d202027, d240357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202027, d240357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro64466 (p : Pattern) (ha : d25319 p = 1) (hb : d208034 p = 1) : d240363 p = 1 := by
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
  have h7 (q : Pattern) (ha : d25148 q = 1) (hb : d208034 q = 1) : d25314 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25148, d25314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25148, d25314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64436 q ha hb
  have h8 (q : Pattern) (ha : d25105 q = 1) (hb : d208034 q = 1) : d25222 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25105, d25222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64436 q ha hb
    | true =>
      simp only [d25105, d25222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d25149 q = 1) (hb : d208034 q = 1) : d25315 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25149, d25315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25149, d25315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d25106 q = 1) (hb : d208034 q = 1) : d25223 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25106, d25223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d25106, d25223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d25150 q = 1) (hb : d208034 q = 1) : d25316 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d25150, d25316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d25150, d25316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d25151 q = 1) (hb : d208034 q = 1) : d25317 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d25151, d25317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d25151, d25317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d25313 q = 1) (hb : d208034 q = 1) : d25590 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d25313, d25590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25313, d25590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d25318 q = 1) (hb : d208034 q = 1) : d25318 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d25319 q = 1) (hb : d208034 q = 1) : d240363 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d25319, d240363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d25319, d240363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro64467 (p : Pattern) (ha : d25325 p = 1) (hb : d208034 p = 1) : d240369 p = 1 := by
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
  have h9 (q : Pattern) (ha : d74 q = 1) (hb : d208034 q = 1) : d74 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d25157 q = 1) (hb : d208034 q = 1) : d240252 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d25157, d240252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25157, d240252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d25324 q = 1) (hb : d208034 q = 1) : d240368 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d25324, d240368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d25324, d240368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d25325 q = 1) (hb : d208034 q = 1) : d240369 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d25325, d240369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d25325, d240369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h12 p ha hb
theorem andIntro64468 (p : Pattern) (ha : d25331 p = 1) (hb : d208034 p = 1) : d240375 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25326 q = 1) (hb : d208034 q = 1) : d240370 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25326, d240370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64467 q ha hb
    | true =>
      simp only [d25326, d240370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25327 q = 1) (hb : d208034 q = 1) : d240371 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25327, d240371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25327, d240371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25160 q = 1) (hb : d208034 q = 1) : d240255 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25160, d240255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64445 q ha hb
    | true =>
      simp only [d25160, d240255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25161 q = 1) (hb : d208034 q = 1) : d240256 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25161, d240256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25161, d240256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25328 q = 1) (hb : d208034 q = 1) : d240372 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25328, d240372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25328, d240372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25329 q = 1) (hb : d208034 q = 1) : d240373 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25329, d240373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25329, d240373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25330 q = 1) (hb : d208034 q = 1) : d240374 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25330, d240374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25330, d240374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d25331 q = 1) (hb : d208034 q = 1) : d240375 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25331, d240375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25331, d240375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro64469 (p : Pattern) (ha : d25356 p = 1) (hb : d208034 p = 1) : d240381 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25160 q = 1) (hb : d208034 q = 1) : d240255 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25160, d240255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64445 q ha hb
    | true =>
      simp only [d25160, d240255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25161 q = 1) (hb : d208034 q = 1) : d240256 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25161, d240256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25161, d240256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25353 q = 1) (hb : d208034 q = 1) : d240378 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25353, d240378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25353, d240378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25354 q = 1) (hb : d208034 q = 1) : d240379 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25354, d240379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25354, d240379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25355 q = 1) (hb : d208034 q = 1) : d240380 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25355, d240380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25355, d240380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d25356 q = 1) (hb : d208034 q = 1) : d240381 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25356, d240381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25356, d240381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro64470 (p : Pattern) (ha : d202037 p = 1) (hb : d208034 p = 1) : d240387 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25332 q = 1) (hb : d208034 q = 1) : d240376 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25332, d240376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64468 q ha hb
    | true =>
      simp only [d25332, d240376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64446 q ha hb
  have h2 (q : Pattern) (ha : d202033 q = 1) (hb : d208034 q = 1) : d240377 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202033, d240377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d202033, d240377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d25357 q = 1) (hb : d208034 q = 1) : d240382 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25357, d240382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64469 q ha hb
    | true =>
      simp only [d25357, d240382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25358 q = 1) (hb : d208034 q = 1) : d240383 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25358, d240383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25358, d240383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d202034 q = 1) (hb : d208034 q = 1) : d240384 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202034, d240384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d202034, d240384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d202035 q = 1) (hb : d208034 q = 1) : d240385 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202035, d240385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202035, d240385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d202036 q = 1) (hb : d208034 q = 1) : d240386 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202036, d240386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202036, d240386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d202037 q = 1) (hb : d208034 q = 1) : d240387 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d202037, d240387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202037, d240387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro64471 (p : Pattern) (ha : d202043 p = 1) (hb : d208034 p = 1) : d240393 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25188 q = 1) (hb : d208034 q = 1) : d240283 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d25188, d240283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25188, d240283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64449 q ha hb
  have h2 (q : Pattern) (ha : d25189 q = 1) (hb : d208034 q = 1) : d240284 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d25189, d240284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d25189, d240284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d25195 q = 1) (hb : d208034 q = 1) : d240290 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d25195, d240290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64449 q ha hb
    | true =>
      simp only [d25195, d240290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64450 q ha hb
  have h4 (q : Pattern) (ha : d25196 q = 1) (hb : d208034 q = 1) : d240291 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d25196, d240291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25196, d240291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25197 q = 1) (hb : d208034 q = 1) : d240292 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d25197, d240292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25197, d240292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d202021 q = 1) (hb : d208034 q = 1) : d240349 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d202021, d240349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64459 q ha hb
    | true =>
      simp only [d202021, d240349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64464 q ha hb
  have h7 (q : Pattern) (ha : d111 q = 1) (hb : d208034 q = 1) : d111 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d25297 q = 1) (hb : d208034 q = 1) : d240351 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d25297, d240351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64451 q ha hb
    | true =>
      simp only [d25297, d240351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d202022 q = 1) (hb : d208034 q = 1) : d240352 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d202022, d240352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d202022, d240352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d202023 q = 1) (hb : d208034 q = 1) : d240353 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d202023, d240353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d202023, d240353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d202024 q = 1) (hb : d208034 q = 1) : d240354 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d202024, d240354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d202024, d240354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d202028 q = 1) (hb : d208034 q = 1) : d240358 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d202028, d240358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202028, d240358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64465 q ha hb
  have h13 (q : Pattern) (ha : d407 q = 1) (hb : d208034 q = 1) : d407 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d202029 q = 1) (hb : d208034 q = 1) : d240359 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d202029, d240359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d202029, d240359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d202030 q = 1) (hb : d208034 q = 1) : d240360 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d202030, d240360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d202030, d240360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d202031 q = 1) (hb : d208034 q = 1) : d240361 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d202031, d240361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d202031, d240361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d202032 q = 1) (hb : d208034 q = 1) : d240362 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d202032, d240362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d202032, d240362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d202038 q = 1) (hb : d208034 q = 1) : d240388 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d202038, d240388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202038, d240388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64470 q ha hb
  have h19 (q : Pattern) (ha : d463 q = 1) (hb : d208034 q = 1) : d463 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d202039 q = 1) (hb : d208034 q = 1) : d240389 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d202039, d240389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d202039, d240389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d202040 q = 1) (hb : d208034 q = 1) : d240390 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d202040, d240390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d202040, d240390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d202041 q = 1) (hb : d208034 q = 1) : d240391 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d202041, d240391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d202041, d240391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d202042 q = 1) (hb : d208034 q = 1) : d240392 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d202042, d240392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d202042, d240392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d202043 q = 1) (hb : d208034 q = 1) : d240393 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d202043, d240393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d202043, d240393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  exact h24 p ha hb
theorem andIntro64472 (p : Pattern) (ha : d202049 p = 1) (hb : d208034 p = 1) : d240399 p = 1 := by
  have h0 (q : Pattern) (ha : d99 q = 1) (hb : d208034 q = 1) : d99 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d202006 q = 1) (hb : d208034 q = 1) : d240273 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d202006, d240273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d202006, d240273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64448 q ha hb
  have h3 (q : Pattern) (ha : d202007 q = 1) (hb : d208034 q = 1) : d240274 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d202007, d240274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d202007, d240274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d202008 q = 1) (hb : d208034 q = 1) : d240275 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d202008, d240275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d202008, d240275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d202009 q = 1) (hb : d208034 q = 1) : d240276 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d202009, d240276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d202009, d240276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d202010 q = 1) (hb : d208034 q = 1) : d240277 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d202010, d240277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202010, d240277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d202044 q = 1) (hb : d208034 q = 1) : d240394 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d202044, d240394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d202044, d240394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64471 q ha hb
  have h8 (q : Pattern) (ha : d202045 q = 1) (hb : d208034 q = 1) : d240395 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d202045, d240395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d202045, d240395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d202046 q = 1) (hb : d208034 q = 1) : d240396 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d202046, d240396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d202046, d240396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d202047 q = 1) (hb : d208034 q = 1) : d240397 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d202047, d240397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d202047, d240397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d202048 q = 1) (hb : d208034 q = 1) : d240398 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d202048, d240398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d202048, d240398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d202049 q = 1) (hb : d208034 q = 1) : d240399 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d202049, d240399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d202049, d240399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro64473 (p : Pattern) (ha : d25377 p = 1) (hb : d208034 p = 1) : d240402 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25228 q = 1) (hb : d208034 q = 1) : d240306 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d25228, d240306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64455 q ha hb
    | true =>
      simp only [d25228, d240306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64437 q ha hb
  have h2 (q : Pattern) (ha : d25229 q = 1) (hb : d208034 q = 1) : d240307 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d25229, d240307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25229, d240307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25230 q = 1) (hb : d208034 q = 1) : d240308 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d25230, d240308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25230, d240308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d30 q = 1) (hb : d208034 q = 1) : d30 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d25111 q = 1) (hb : d208034 q = 1) : d240212 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d25111, d240212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64437 q ha hb
    | true =>
      simp only [d25111, d240212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25112 q = 1) (hb : d208034 q = 1) : d240213 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d25112, d240213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25112, d240213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d25113 q = 1) (hb : d208034 q = 1) : d240214 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d25113, d240214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25113, d240214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d25231 q = 1) (hb : d208034 q = 1) : d240309 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d25231, d240309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25231, d240309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d25375 q = 1) (hb : d208034 q = 1) : d240400 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d25375, d240400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25375, d240400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d25376 q = 1) (hb : d208034 q = 1) : d240401 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d25376, d240401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d25376, d240401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d25377 q = 1) (hb : d208034 q = 1) : d240402 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d25377, d240402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d25377, d240402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h11 p ha hb
theorem andIntro64474 (p : Pattern) (ha : d25381 p = 1) (hb : d208034 p = 1) : d240406 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30 q = 1) (hb : d208034 q = 1) : d30 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d25111 q = 1) (hb : d208034 q = 1) : d240212 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d25111, d240212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64437 q ha hb
    | true =>
      simp only [d25111, d240212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25112 q = 1) (hb : d208034 q = 1) : d240213 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d25112, d240213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25112, d240213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d25113 q = 1) (hb : d208034 q = 1) : d240214 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d25113, d240214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25113, d240214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25375 q = 1) (hb : d208034 q = 1) : d240400 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d25375, d240400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25375, d240400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d25380 q = 1) (hb : d208034 q = 1) : d240405 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d25380, d240405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25380, d240405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25381 q = 1) (hb : d208034 q = 1) : d240406 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d25381, d240406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25381, d240406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro64475 (p : Pattern) (ha : d25387 p = 1) (hb : d208034 p = 1) : d240412 p = 1 := by
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
  have h6 (q : Pattern) (ha : d25385 q = 1) (hb : d208034 q = 1) : d240410 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25385, d240410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25385, d240410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25386 q = 1) (hb : d208034 q = 1) : d240411 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25386, d240411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25386, d240411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d25387 q = 1) (hb : d208034 q = 1) : d240412 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25387, d240412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25387, d240412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro64476 (p : Pattern) (ha : d25391 p = 1) (hb : d208034 p = 1) : d240416 p = 1 := by
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
  have h4 (q : Pattern) (ha : d25389 q = 1) (hb : d208034 q = 1) : d240414 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25389, d240414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25389, d240414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25390 q = 1) (hb : d208034 q = 1) : d240415 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25390, d240415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25390, d240415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d25391 q = 1) (hb : d208034 q = 1) : d240416 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25391, d240416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25391, d240416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro64477 (p : Pattern) (ha : d25397 p = 1) (hb : d208034 p = 1) : d240422 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25392 q = 1) (hb : d208034 q = 1) : d240417 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25392, d240417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64475 q ha hb
    | true =>
      simp only [d25392, d240417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64476 q ha hb
  have h2 (q : Pattern) (ha : d25393 q = 1) (hb : d208034 q = 1) : d240418 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25393, d240418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25393, d240418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25394 q = 1) (hb : d208034 q = 1) : d240419 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25394, d240419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25394, d240419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25395 q = 1) (hb : d208034 q = 1) : d240420 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25395, d240420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25395, d240420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25396 q = 1) (hb : d208034 q = 1) : d240421 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d25396, d240421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25396, d240421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25397 q = 1) (hb : d208034 q = 1) : d240422 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d25397, d240422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25397, d240422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro64478 (p : Pattern) (ha : d25400 p = 1) (hb : d208034 p = 1) : d240425 p = 1 := by
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
  have h6 (q : Pattern) (ha : d25385 q = 1) (hb : d208034 q = 1) : d240410 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25385, d240410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25385, d240410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25386 q = 1) (hb : d208034 q = 1) : d240411 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25386, d240411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25386, d240411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d25400 q = 1) (hb : d208034 q = 1) : d240425 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25400, d240425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25400, d240425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro64479 (p : Pattern) (ha : d25401 p = 1) (hb : d208034 p = 1) : d240426 p = 1 := by
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
  have h4 (q : Pattern) (ha : d25389 q = 1) (hb : d208034 q = 1) : d240414 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25389, d240414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25389, d240414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25390 q = 1) (hb : d208034 q = 1) : d240415 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25390, d240415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25390, d240415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d25401 q = 1) (hb : d208034 q = 1) : d240426 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25401, d240426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25401, d240426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro64480 (p : Pattern) (ha : d25407 p = 1) (hb : d208034 p = 1) : d240432 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25392 q = 1) (hb : d208034 q = 1) : d240417 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25392, d240417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64475 q ha hb
    | true =>
      simp only [d25392, d240417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64476 q ha hb
  have h2 (q : Pattern) (ha : d25393 q = 1) (hb : d208034 q = 1) : d240418 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25393, d240418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25393, d240418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25394 q = 1) (hb : d208034 q = 1) : d240419 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25394, d240419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25394, d240419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25395 q = 1) (hb : d208034 q = 1) : d240420 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25395, d240420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25395, d240420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25396 q = 1) (hb : d208034 q = 1) : d240421 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d25396, d240421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25396, d240421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25402 q = 1) (hb : d208034 q = 1) : d240427 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25402, d240427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64478 q ha hb
    | true =>
      simp only [d25402, d240427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64479 q ha hb
  have h7 (q : Pattern) (ha : d25403 q = 1) (hb : d208034 q = 1) : d240428 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25403, d240428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25403, d240428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d25404 q = 1) (hb : d208034 q = 1) : d240429 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25404, d240429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25404, d240429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d25405 q = 1) (hb : d208034 q = 1) : d240430 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25405, d240430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25405, d240430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d25406 q = 1) (hb : d208034 q = 1) : d240431 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d25406, d240431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25406, d240431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d25407 q = 1) (hb : d208034 q = 1) : d240432 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d25407, d240432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25407, d240432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro64481 (p : Pattern) (ha : d25556 p = 1) (hb : d208034 p = 1) : d240505 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25392 q = 1) (hb : d208034 q = 1) : d240417 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25392, d240417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64475 q ha hb
    | true =>
      simp only [d25392, d240417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64476 q ha hb
  have h2 (q : Pattern) (ha : d25393 q = 1) (hb : d208034 q = 1) : d240418 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25393, d240418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25393, d240418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25394 q = 1) (hb : d208034 q = 1) : d240419 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25394, d240419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25394, d240419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25395 q = 1) (hb : d208034 q = 1) : d240420 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25395, d240420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25395, d240420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25396 q = 1) (hb : d208034 q = 1) : d240421 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d25396, d240421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25396, d240421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25551 q = 1) (hb : d208034 q = 1) : d240500 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25551, d240500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64476 q ha hb
    | true =>
      simp only [d25551, d240500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25552 q = 1) (hb : d208034 q = 1) : d240501 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25552, d240501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25552, d240501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d25553 q = 1) (hb : d208034 q = 1) : d240502 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25553, d240502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25553, d240502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d25554 q = 1) (hb : d208034 q = 1) : d240503 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25554, d240503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25554, d240503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d25555 q = 1) (hb : d208034 q = 1) : d240504 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d25555, d240504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25555, d240504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d25556 q = 1) (hb : d208034 q = 1) : d240505 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d25556, d240505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25556, d240505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro64482 (p : Pattern) (ha : d25562 p = 1) (hb : d208034 p = 1) : d240511 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25551 q = 1) (hb : d208034 q = 1) : d240500 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25551, d240500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64476 q ha hb
    | true =>
      simp only [d25551, d240500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25552 q = 1) (hb : d208034 q = 1) : d240501 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25552, d240501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25552, d240501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25553 q = 1) (hb : d208034 q = 1) : d240502 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25553, d240502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25553, d240502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25554 q = 1) (hb : d208034 q = 1) : d240503 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25554, d240503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25554, d240503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25555 q = 1) (hb : d208034 q = 1) : d240504 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d25555, d240504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25555, d240504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25557 q = 1) (hb : d208034 q = 1) : d240506 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25557, d240506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64479 q ha hb
    | true =>
      simp only [d25557, d240506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25558 q = 1) (hb : d208034 q = 1) : d240507 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25558, d240507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25558, d240507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d25559 q = 1) (hb : d208034 q = 1) : d240508 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25559, d240508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25559, d240508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d25560 q = 1) (hb : d208034 q = 1) : d240509 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25560, d240509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25560, d240509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d25561 q = 1) (hb : d208034 q = 1) : d240510 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d25561, d240510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25561, d240510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d25562 q = 1) (hb : d208034 q = 1) : d240511 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d25562, d240511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25562, d240511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro64483 (p : Pattern) (ha : d25571 p = 1) (hb : d208034 p = 1) : d240520 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25557 q = 1) (hb : d208034 q = 1) : d240506 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25557, d240506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64479 q ha hb
    | true =>
      simp only [d25557, d240506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25558 q = 1) (hb : d208034 q = 1) : d240507 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25558, d240507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25558, d240507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25559 q = 1) (hb : d208034 q = 1) : d240508 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25559, d240508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25559, d240508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25560 q = 1) (hb : d208034 q = 1) : d240509 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25560, d240509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25560, d240509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25561 q = 1) (hb : d208034 q = 1) : d240510 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d25561, d240510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25561, d240510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25571 q = 1) (hb : d208034 q = 1) : d240520 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d25571, d240520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25571, d240520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro64484 (p : Pattern) (ha : d25614 p = 1) (hb : d208034 p = 1) : d240545 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d71 q = 1) (hb : d208034 q = 1) : d71 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d25154 q = 1) (hb : d208034 q = 1) : d240249 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d25154, d240249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64444 q ha hb
    | true =>
      simp only [d25154, d240249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25155 q = 1) (hb : d208034 q = 1) : d240250 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d25155, d240250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25155, d240250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d25156 q = 1) (hb : d208034 q = 1) : d240251 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d25156, d240251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25156, d240251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25604 q = 1) (hb : d208034 q = 1) : d240535 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d25604, d240535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25604, d240535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d25613 q = 1) (hb : d208034 q = 1) : d240544 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d25613, d240544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25613, d240544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25614 q = 1) (hb : d208034 q = 1) : d240545 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d25614, d240545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25614, d240545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro64485 (p : Pattern) (ha : d25670 p = 1) (hb : d208034 p = 1) : d240568 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25615 q = 1) (hb : d208034 q = 1) : d240546 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25615, d240546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64484 q ha hb
    | true =>
      simp only [d25615, d240546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25616 q = 1) (hb : d208034 q = 1) : d240547 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25616, d240547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25616, d240547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25667 q = 1) (hb : d208034 q = 1) : d240565 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25667, d240565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25667, d240565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25668 q = 1) (hb : d208034 q = 1) : d240566 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25668, d240566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25668, d240566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25669 q = 1) (hb : d208034 q = 1) : d240567 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25669, d240567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25669, d240567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d25670 q = 1) (hb : d208034 q = 1) : d240568 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25670, d240568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25670, d240568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro64486 (p : Pattern) (ha : d25676 p = 1) (hb : d208034 p = 1) : d240574 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25671 q = 1) (hb : d208034 q = 1) : d240569 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25671, d240569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64485 q ha hb
    | true =>
      simp only [d25671, d240569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25672 q = 1) (hb : d208034 q = 1) : d240570 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25672, d240570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25672, d240570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25673 q = 1) (hb : d208034 q = 1) : d240571 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25673, d240571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25673, d240571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25674 q = 1) (hb : d208034 q = 1) : d240572 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25674, d240572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25674, d240572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25675 q = 1) (hb : d208034 q = 1) : d240573 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d25675, d240573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25675, d240573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25676 q = 1) (hb : d208034 q = 1) : d240574 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d25676, d240574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25676, d240574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro64487 (p : Pattern) (ha : d25412 p = 1) (hb : d208034 p = 1) : d240437 p = 1 := by
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
  have h6 (q : Pattern) (ha : d25385 q = 1) (hb : d208034 q = 1) : d240410 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25385, d240410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25385, d240410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25411 q = 1) (hb : d208034 q = 1) : d240436 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25411, d240436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25411, d240436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d25412 q = 1) (hb : d208034 q = 1) : d240437 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25412, d240437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25412, d240437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro64488 (p : Pattern) (ha : d25414 p = 1) (hb : d208034 p = 1) : d240439 p = 1 := by
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
  have h4 (q : Pattern) (ha : d25389 q = 1) (hb : d208034 q = 1) : d240414 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25389, d240414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25389, d240414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25413 q = 1) (hb : d208034 q = 1) : d240438 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25413, d240438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25413, d240438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25414 q = 1) (hb : d208034 q = 1) : d240439 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25414, d240439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25414, d240439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro64489 (p : Pattern) (ha : d25421 p = 1) (hb : d208034 p = 1) : d240446 p = 1 := by
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
  have h8 (q : Pattern) (ha : d25421 q = 1) (hb : d208034 q = 1) : d240446 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25421, d240446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25421, d240446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro64490 (p : Pattern) (ha : d25424 p = 1) (hb : d208034 p = 1) : d240449 p = 1 := by
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
  have h6 (q : Pattern) (ha : d25424 q = 1) (hb : d208034 q = 1) : d240449 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25424, d240449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25424, d240449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro64491 (p : Pattern) (ha : d25438 p = 1) (hb : d208034 p = 1) : d25783 p = 1 := by
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
  have h5 (q : Pattern) (ha : d25210 q = 1) (hb : d152852 q = 1) : d25210 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d25435 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d25436 q = 1) (hb : d208034 q = 1) : d25449 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d25436, d208034, d25449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25436, d208034, d25449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d25437 q = 1) (hb : d208034 q = 1) : d25450 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d25437, d25450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25437, d25450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h9 (q : Pattern) (ha : d25438 q = 1) (hb : d208034 q = 1) : d25783 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d25438, d25783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25438, d25783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro64492 (p : Pattern) (ha : d25443 p = 1) (hb : d208034 p = 1) : d25451 p = 1 := by
  have h0 (q : Pattern) (ha : d25210 q = 1) (hb : d152852 q = 1) : d25210 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d9796 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d25211 q = 1) (hb : d208034 q = 1) : d25449 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d25211, d208034, d25449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25211, d208034, d25449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d25212 q = 1) (hb : d208034 q = 1) : d25450 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d25212, d25450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25212, d25450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25220 q = 1) (hb : d208034 q = 1) : d25220 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d25443 q = 1) (hb : d208034 q = 1) : d25451 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d25443, d25451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25443, d25451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro64493 (p : Pattern) (ha : d25457 p = 1) (hb : d208034 p = 1) : d240453 p = 1 := by
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
  have h10 (q : Pattern) (ha : d25456 q = 1) (hb : d208034 q = 1) : d25456 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d25457 q = 1) (hb : d208034 q = 1) : d240453 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d25457, d240453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d25457, d240453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro64494 (p : Pattern) (ha : d25467 p = 1) (hb : d208034 p = 1) : d240459 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25458 q = 1) (hb : d208034 q = 1) : d240454 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d25458, d240454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64493 q ha hb
    | true =>
      simp only [d25458, d240454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64455 q ha hb
  have h2 (q : Pattern) (ha : d25459 q = 1) (hb : d208034 q = 1) : d240455 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d25459, d240455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25459, d240455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25460 q = 1) (hb : d208034 q = 1) : d240456 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d25460, d240456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25460, d240456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d25461 q = 1) (hb : d208034 q = 1) : d25461 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d25462 q = 1) (hb : d208034 q = 1) : d240306 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d25462, d240306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64455 q ha hb
    | true =>
      simp only [d25462, d240306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25463 q = 1) (hb : d208034 q = 1) : d240307 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d25463, d240307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25463, d240307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d25464 q = 1) (hb : d208034 q = 1) : d240308 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d25464, d240308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25464, d240308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d25465 q = 1) (hb : d208034 q = 1) : d240457 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d25465, d240457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25465, d240457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d25228 q = 1) (hb : d208034 q = 1) : d240306 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d25228, d240306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64455 q ha hb
    | true =>
      simp only [d25228, d240306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64437 q ha hb
  have h10 (q : Pattern) (ha : d25229 q = 1) (hb : d208034 q = 1) : d240307 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d25229, d240307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25229, d240307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d25230 q = 1) (hb : d208034 q = 1) : d240308 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d25230, d240308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25230, d240308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d30 q = 1) (hb : d208034 q = 1) : d30 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d25111 q = 1) (hb : d208034 q = 1) : d240212 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d25111, d240212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64437 q ha hb
    | true =>
      simp only [d25111, d240212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d25112 q = 1) (hb : d208034 q = 1) : d240213 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d25112, d240213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25112, d240213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d25113 q = 1) (hb : d208034 q = 1) : d240214 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d25113, d240214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25113, d240214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d25231 q = 1) (hb : d208034 q = 1) : d240309 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d25231, d240309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d25231, d240309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d25466 q = 1) (hb : d208034 q = 1) : d240458 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d25466, d240458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d25466, d240458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d25467 q = 1) (hb : d208034 q = 1) : d240459 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d25467, d240459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d25467, d240459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h18 p ha hb
theorem andIntro64495 (p : Pattern) (ha : d25473 p = 1) (hb : d208034 p = 1) : d240465 p = 1 := by
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
  have h8 (q : Pattern) (ha : d25473 q = 1) (hb : d208034 q = 1) : d240465 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25473, d240465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25473, d240465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro64496 (p : Pattern) (ha : d25519 p = 1) (hb : d208034 p = 1) : d240471 p = 1 := by
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
  have h6 (q : Pattern) (ha : d25519 q = 1) (hb : d208034 q = 1) : d240471 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25519, d240471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25519, d240471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro64497 (p : Pattern) (ha : d202054 p = 1) (hb : d208034 p = 1) : d240477 p = 1 := by
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
  have h15 (q : Pattern) (ha : d202054 q = 1) (hb : d208034 q = 1) : d240477 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d202054, d240477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202054, d240477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro64498 (p : Pattern) (ha : d25526 p = 1) (hb : d208034 p = 1) : d240478 p = 1 := by
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
  have h6 (q : Pattern) (ha : d25385 q = 1) (hb : d208034 q = 1) : d240410 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25385, d240410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25385, d240410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25411 q = 1) (hb : d208034 q = 1) : d240436 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25411, d240436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25411, d240436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d25526 q = 1) (hb : d208034 q = 1) : d240478 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25526, d240478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25526, d240478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro64499 (p : Pattern) (ha : d25527 p = 1) (hb : d208034 p = 1) : d240479 p = 1 := by
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
  have h4 (q : Pattern) (ha : d25389 q = 1) (hb : d208034 q = 1) : d240414 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25389, d240414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25389, d240414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25413 q = 1) (hb : d208034 q = 1) : d240438 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25413, d240438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25413, d240438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25527 q = 1) (hb : d208034 q = 1) : d240479 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25527, d240479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25527, d240479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
end NetHack.Soko22Hazard87
