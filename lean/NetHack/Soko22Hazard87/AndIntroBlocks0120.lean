import NetHack.Soko22Hazard87.AndIntroBlocks0119
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro30000 (p : Pattern) (ha : d148528 p = 1) (hb : d152832 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148523 q = 1) (hb : d152827 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d148523, d152827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29999 q ha hb
    | true =>
      simp only [d148523, d152827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d148524 q = 1) (hb : d152828 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d148524, d152828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d148524, d152828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d148525 q = 1) (hb : d152829 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d148525, d152829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148525, d152829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148526 q = 1) (hb : d152830 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d148526, d152830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148526, d152830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d148527 q = 1) (hb : d152831 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d148527, d152831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d148527, d152831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d148528 q = 1) (hb : d152832 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d148528, d152832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148528, d152832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro30001 (p : Pattern) (ha : d148534 p = 1) (hb : d152838 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148529 q = 1) (hb : d152833 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d148529, d152833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30000 q ha hb
    | true =>
      simp only [d148529, d152833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d148530 q = 1) (hb : d152834 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d148530, d152834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d148530, d152834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d148531 q = 1) (hb : d152835 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d148531, d152835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148531, d152835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148532 q = 1) (hb : d152836 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d148532, d152836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148532, d152836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d148533 q = 1) (hb : d152837 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d148533, d152837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d148533, d152837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d148534 q = 1) (hb : d152838 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d148534, d152838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148534, d152838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro30002 (p : Pattern) (ha : d148540 p = 1) (hb : d152844 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148535 q = 1) (hb : d152839 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d148535, d152839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30001 q ha hb
    | true =>
      simp only [d148535, d152839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d148536 q = 1) (hb : d152840 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d148536, d152840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d148536, d152840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d148537 q = 1) (hb : d152841 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d148537, d152841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148537, d152841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148538 q = 1) (hb : d152842 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d148538, d152842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148538, d152842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d148539 q = 1) (hb : d152843 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d148539, d152843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d148539, d152843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d148540 q = 1) (hb : d152844 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d148540, d152844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148540, d152844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro30003 (p : Pattern) (ha : d148546 p = 1) (hb : d152850 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148541 q = 1) (hb : d152845 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d148541, d152845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30002 q ha hb
    | true =>
      simp only [d148541, d152845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d148542 q = 1) (hb : d152846 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d148542, d152846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d148542, d152846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d148543 q = 1) (hb : d152847 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d148543, d152847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148543, d152847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148544 q = 1) (hb : d152848 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d148544, d152848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148544, d152848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d148545 q = 1) (hb : d152849 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d148545, d152849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d148545, d152849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d148546 q = 1) (hb : d152850 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d148546, d152850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148546, d152850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro30004 (p : Pattern) (ha : d150039 p = 1) (hb : d151355 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d20982 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d20988 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d21009 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d151297 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d150035 q = 1) (hb : d151351 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150035, d151351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d150035, d151351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d21031 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d150036 q = 1) (hb : d151352 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150036, d151352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150036, d151352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d150037 q = 1) (hb : d151353 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150037, d151353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d150037, d151353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d150038 q = 1) (hb : d151354 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150038, d151354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150038, d151354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d150039 q = 1) (hb : d151355 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150039, d151355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150039, d151355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro30005 (p : Pattern) (ha : d150044 p = 1) (hb : d151362 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d20982 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d20988 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d21009 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d151297 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d150035 q = 1) (hb : d151351 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150035, d151351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d150035, d151351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d21031 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d150036 q = 1) (hb : d151352 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150036, d151352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150036, d151352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d150037 q = 1) (hb : d151353 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150037, d151353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150037, d151353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d150038 q = 1) (hb : d151354 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150038, d151354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150038, d151354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d21040 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d21044 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d21046 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d151304 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d150040 q = 1) (hb : d151358 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150040, d151358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d150040, d151358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d21052 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d150041 q = 1) (hb : d151359 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150041, d151359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d150041, d151359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d150042 q = 1) (hb : d151360 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150042, d151360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d150042, d151360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d150043 q = 1) (hb : d151361 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150043, d151361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d150043, d151361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d150044 q = 1) (hb : d151362 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150044, d151362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d150044, d151362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro30006 (p : Pattern) (ha : d150051 p = 1) (hb : d152628 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d21046 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d151304 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d150040 q = 1) (hb : d151358 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150040, d151358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150040, d151358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d21052 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d150041 q = 1) (hb : d151359 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150041, d151359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150041, d151359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d150049 q = 1) (hb : d151360 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150049, d151360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150049, d151360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d150050 q = 1) (hb : d151361 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150050, d151361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150050, d151361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d150051 q = 1) (hb : d152628 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150051, d152628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150051, d152628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro30007 (p : Pattern) (ha : d150061 p = 1) (hb : d152638 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d21090 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d151334 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d150057 q = 1) (hb : d152634 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150057, d152634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150057, d152634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d21112 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d150058 q = 1) (hb : d152635 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150058, d152635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150058, d152635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d150059 q = 1) (hb : d152636 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150059, d152636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150059, d152636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d150060 q = 1) (hb : d152637 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150060, d152637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150060, d152637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d150061 q = 1) (hb : d152638 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150061, d152638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150061, d152638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro30008 (p : Pattern) (ha : d150067 p = 1) (hb : d152644 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d20976 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d150045 q = 1) (hb : d151363 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150045, d151363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30004 q ha hb
    | true =>
      simp only [d150045, d151363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30005 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d21059 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d150046 q = 1) (hb : d151364 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150046, d151364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150046, d151364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d150047 q = 1) (hb : d152626 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150047, d152626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150047, d152626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d150048 q = 1) (hb : d152627 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150048, d152627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150048, d152627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d150052 q = 1) (hb : d152629 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150052, d152629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150052, d152629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30006 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d407 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d150053 q = 1) (hb : d152630 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150053, d152630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d150053, d152630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d150054 q = 1) (hb : d152631 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150054, d152631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d150054, d152631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d150055 q = 1) (hb : d152632 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150055, d152632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d150055, d152632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d150056 q = 1) (hb : d152633 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150056, d152633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d150056, d152633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d150062 q = 1) (hb : d152639 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150062, d152639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150062, d152639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30007 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d463 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d150063 q = 1) (hb : d152640 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150063, d152640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d150063, d152640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d150064 q = 1) (hb : d152641 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150064, d152641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d150064, d152641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d150065 q = 1) (hb : d152642 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150065, d152642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d150065, d152642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d150066 q = 1) (hb : d152643 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150066, d152643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d150066, d152643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d150067 q = 1) (hb : d152644 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d150067, d152644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d150067, d152644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro30009 (p : Pattern) (ha : d150073 p = 1) (hb : d152650 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d99 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53648 q = 1) (hb : d150030 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53648, d150030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53648, d150030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28446 q ha hb
  have h3 (q : Pattern) (ha : d53649 q = 1) (hb : d150031 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53649, d150031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53649, d150031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53650 q = 1) (hb : d150032 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53650, d150032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53650, d150032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53651 q = 1) (hb : d150033 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53651, d150033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53651, d150033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53652 q = 1) (hb : d150034 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53652, d150034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53652, d150034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d150068 q = 1) (hb : d152645 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d150068, d152645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150068, d152645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30008 q ha hb
  have h8 (q : Pattern) (ha : d150069 q = 1) (hb : d152646 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d150069, d152646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150069, d152646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d150070 q = 1) (hb : d152647 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d150070, d152647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150070, d152647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d150071 q = 1) (hb : d152648 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d150071, d152648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150071, d152648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d150072 q = 1) (hb : d152649 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d150072, d152649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150072, d152649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d150073 q = 1) (hb : d152650 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d150073, d152650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d150073, d152650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro30010 (p : Pattern) (ha : d150078 p = 1) (hb : d151493 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d21172 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d21181 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d21211 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d151488 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d150074 q = 1) (hb : d151489 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150074, d151489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d150074, d151489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d21253 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d150075 q = 1) (hb : d151490 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150075, d151490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150075, d151490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d150076 q = 1) (hb : d151491 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150076, d151491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d150076, d151491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d150077 q = 1) (hb : d151492 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150077, d151492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150077, d151492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d150078 q = 1) (hb : d151493 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150078, d151493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150078, d151493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro30011 (p : Pattern) (ha : d150083 p = 1) (hb : d151503 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d21172 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d21181 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d21211 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d151488 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d150074 q = 1) (hb : d151489 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150074, d151489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d150074, d151489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d21253 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d150075 q = 1) (hb : d151490 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150075, d151490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150075, d151490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d150076 q = 1) (hb : d151491 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150076, d151491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150076, d151491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d150077 q = 1) (hb : d151492 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150077, d151492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150077, d151492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d21263 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d21268 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d21270 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d151498 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d150079 q = 1) (hb : d151499 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150079, d151499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d150079, d151499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d21277 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d150080 q = 1) (hb : d151500 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150080, d151500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d150080, d151500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d150081 q = 1) (hb : d151501 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150081, d151501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d150081, d151501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d150082 q = 1) (hb : d151502 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150082, d151502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d150082, d151502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d150083 q = 1) (hb : d151503 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150083, d151503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d150083, d151503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro30012 (p : Pattern) (ha : d150090 p = 1) (hb : d152653 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d21270 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d151498 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d150079 q = 1) (hb : d151499 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150079, d151499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150079, d151499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d21277 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d150080 q = 1) (hb : d151500 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150080, d151500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150080, d151500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d150088 q = 1) (hb : d151501 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150088, d151501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150088, d151501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d150089 q = 1) (hb : d151502 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150089, d151502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150089, d151502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d150090 q = 1) (hb : d152653 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150090, d152653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150090, d152653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro30013 (p : Pattern) (ha : d150100 p = 1) (hb : d152664 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d21349 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d152659 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d150096 q = 1) (hb : d152660 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150096, d152660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150096, d152660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d21389 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d150097 q = 1) (hb : d152661 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150097, d152661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150097, d152661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d150098 q = 1) (hb : d152662 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150098, d152662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150098, d152662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d150099 q = 1) (hb : d152663 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150099, d152663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150099, d152663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d150100 q = 1) (hb : d152664 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150100, d152664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150100, d152664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro30014 (p : Pattern) (ha : d150106 p = 1) (hb : d152670 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d21164 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d150084 q = 1) (hb : d151504 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150084, d151504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30010 q ha hb
    | true =>
      simp only [d150084, d151504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30011 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d21295 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d150085 q = 1) (hb : d151505 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150085, d151505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150085, d151505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d150086 q = 1) (hb : d152651 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150086, d152651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150086, d152651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d150087 q = 1) (hb : d152652 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150087, d152652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150087, d152652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d150091 q = 1) (hb : d152654 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150091, d152654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150091, d152654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30012 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d21304 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d150092 q = 1) (hb : d152655 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150092, d152655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d150092, d152655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d150093 q = 1) (hb : d152656 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150093, d152656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d150093, d152656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d150094 q = 1) (hb : d152657 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150094, d152657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d150094, d152657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d150095 q = 1) (hb : d152658 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150095, d152658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d150095, d152658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d150101 q = 1) (hb : d152665 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150101, d152665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150101, d152665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30013 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d21405 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d150102 q = 1) (hb : d152666 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150102, d152666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d150102, d152666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d150103 q = 1) (hb : d152667 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150103, d152667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d150103, d152667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d150104 q = 1) (hb : d152668 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150104, d152668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d150104, d152668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d150105 q = 1) (hb : d152669 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150105, d152669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d150105, d152669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d150106 q = 1) (hb : d152670 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d150106, d152670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d150106, d152670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro30015 (p : Pattern) (ha : d150112 p = 1) (hb : d152676 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d150107 q = 1) (hb : d152671 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d150107, d152671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150107, d152671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30014 q ha hb
  have h2 (q : Pattern) (ha : d150108 q = 1) (hb : d152672 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d150108, d152672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150108, d152672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d150109 q = 1) (hb : d152673 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d150109, d152673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150109, d152673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d150110 q = 1) (hb : d152674 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d150110, d152674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150110, d152674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d150111 q = 1) (hb : d152675 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d150111, d152675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150111, d152675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d150112 q = 1) (hb : d152676 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d150112, d152676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150112, d152676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro30016 (p : Pattern) (ha : d150118 p = 1) (hb : d151691 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d21471 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d21480 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d21510 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d151686 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d150114 q = 1) (hb : d151687 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150114, d151687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d150114, d151687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d21556 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d150115 q = 1) (hb : d151688 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150115, d151688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150115, d151688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d150116 q = 1) (hb : d151689 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150116, d151689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d150116, d151689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d150117 q = 1) (hb : d151690 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150117, d151690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150117, d151690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d150118 q = 1) (hb : d151691 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150118, d151691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150118, d151691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro30017 (p : Pattern) (ha : d150123 p = 1) (hb : d151701 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d21471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d21480 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d21510 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d151686 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d150114 q = 1) (hb : d151687 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150114, d151687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d150114, d151687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d21556 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d150115 q = 1) (hb : d151688 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150115, d151688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150115, d151688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d150116 q = 1) (hb : d151689 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150116, d151689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150116, d151689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d150117 q = 1) (hb : d151690 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150117, d151690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150117, d151690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d21566 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d21571 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d21573 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d151696 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d150119 q = 1) (hb : d151697 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150119, d151697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d150119, d151697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d21580 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d150120 q = 1) (hb : d151698 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150120, d151698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d150120, d151698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d150121 q = 1) (hb : d151699 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150121, d151699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d150121, d151699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d150122 q = 1) (hb : d151700 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150122, d151700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d150122, d151700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d150123 q = 1) (hb : d151701 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150123, d151701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d150123, d151701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro30018 (p : Pattern) (ha : d150130 p = 1) (hb : d152680 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d21573 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d151696 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d150119 q = 1) (hb : d151697 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150119, d151697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150119, d151697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d21580 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d150120 q = 1) (hb : d151698 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150120, d151698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150120, d151698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d150128 q = 1) (hb : d151699 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150128, d151699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150128, d151699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d150129 q = 1) (hb : d151700 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150129, d151700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150129, d151700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d150130 q = 1) (hb : d152680 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150130, d152680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150130, d152680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro30019 (p : Pattern) (ha : d150140 p = 1) (hb : d152691 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d21662 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d152686 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d150136 q = 1) (hb : d152687 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150136, d152687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150136, d152687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d21706 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d150137 q = 1) (hb : d152688 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150137, d152688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150137, d152688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d150138 q = 1) (hb : d152689 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150138, d152689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150138, d152689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d150139 q = 1) (hb : d152690 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150139, d152690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150139, d152690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d150140 q = 1) (hb : d152691 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150140, d152691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150140, d152691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro30020 (p : Pattern) (ha : d150146 p = 1) (hb : d152697 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d21463 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d150124 q = 1) (hb : d151702 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150124, d151702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30016 q ha hb
    | true =>
      simp only [d150124, d151702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30017 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d21598 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d150125 q = 1) (hb : d151703 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150125, d151703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150125, d151703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d150126 q = 1) (hb : d152678 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150126, d152678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150126, d152678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d150127 q = 1) (hb : d152679 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150127, d152679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150127, d152679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d150131 q = 1) (hb : d152681 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150131, d152681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150131, d152681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30018 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d21607 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d150132 q = 1) (hb : d152682 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150132, d152682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d150132, d152682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d150133 q = 1) (hb : d152683 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150133, d152683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d150133, d152683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d150134 q = 1) (hb : d152684 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150134, d152684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d150134, d152684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d150135 q = 1) (hb : d152685 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150135, d152685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d150135, d152685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d150141 q = 1) (hb : d152692 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150141, d152692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150141, d152692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30019 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d21722 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d150142 q = 1) (hb : d152693 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150142, d152693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d150142, d152693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d150143 q = 1) (hb : d152694 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150143, d152694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d150143, d152694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d150144 q = 1) (hb : d152695 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150144, d152695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d150144, d152695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d150145 q = 1) (hb : d152696 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150145, d152696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d150145, d152696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d150146 q = 1) (hb : d152697 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d150146, d152697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d150146, d152697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro30021 (p : Pattern) (ha : d150152 p = 1) (hb : d152703 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d150147 q = 1) (hb : d152698 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d150147, d152698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150147, d152698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30020 q ha hb
  have h2 (q : Pattern) (ha : d150148 q = 1) (hb : d152699 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d150148, d152699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150148, d152699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d150149 q = 1) (hb : d152700 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d150149, d152700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150149, d152700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d150150 q = 1) (hb : d152701 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d150150, d152701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150150, d152701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d150151 q = 1) (hb : d152702 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d150151, d152702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150151, d152702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d150152 q = 1) (hb : d152703 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d150152, d152703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150152, d152703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro30022 (p : Pattern) (ha : d150159 p = 1) (hb : d151901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d21824 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d21833 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d21878 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d151896 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d150155 q = 1) (hb : d151897 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150155, d151897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d150155, d151897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d21962 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d150156 q = 1) (hb : d151898 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150156, d151898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150156, d151898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d150157 q = 1) (hb : d151899 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150157, d151899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d150157, d151899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d150158 q = 1) (hb : d151900 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150158, d151900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150158, d151900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d150159 q = 1) (hb : d151901 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150159, d151901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150159, d151901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro30023 (p : Pattern) (ha : d150164 p = 1) (hb : d151911 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d21824 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d21833 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d21878 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d151896 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d150155 q = 1) (hb : d151897 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150155, d151897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d150155, d151897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d21962 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d150156 q = 1) (hb : d151898 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150156, d151898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150156, d151898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d150157 q = 1) (hb : d151899 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150157, d151899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150157, d151899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d150158 q = 1) (hb : d151900 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150158, d151900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150158, d151900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d21972 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d21977 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d21980 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d151906 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d150160 q = 1) (hb : d151907 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150160, d151907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d150160, d151907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d21987 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d150161 q = 1) (hb : d151908 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150161, d151908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d150161, d151908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d150162 q = 1) (hb : d151909 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150162, d151909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d150162, d151909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d150163 q = 1) (hb : d151910 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150163, d151910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d150163, d151910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d150164 q = 1) (hb : d151911 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150164, d151911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d150164, d151911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro30024 (p : Pattern) (ha : d150171 p = 1) (hb : d152708 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d21980 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d151906 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d150160 q = 1) (hb : d151907 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150160, d151907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150160, d151907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d21987 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d150161 q = 1) (hb : d151908 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150161, d151908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150161, d151908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d150169 q = 1) (hb : d151909 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150169, d151909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150169, d151909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d150170 q = 1) (hb : d151910 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150170, d151910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150170, d151910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d150171 q = 1) (hb : d152708 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150171, d152708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150171, d152708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro30025 (p : Pattern) (ha : d150181 p = 1) (hb : d152723 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d22110 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d152718 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d150177 q = 1) (hb : d152719 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150177, d152719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150177, d152719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d22188 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d150178 q = 1) (hb : d152720 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150178, d152720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150178, d152720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d150179 q = 1) (hb : d152721 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150179, d152721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150179, d152721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d150180 q = 1) (hb : d152722 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150180, d152722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150180, d152722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d150181 q = 1) (hb : d152723 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150181, d152723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150181, d152723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro30026 (p : Pattern) (ha : d150187 p = 1) (hb : d152729 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d21816 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d150165 q = 1) (hb : d151912 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150165, d151912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30022 q ha hb
    | true =>
      simp only [d150165, d151912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30023 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d22010 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d150166 q = 1) (hb : d151913 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150166, d151913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150166, d151913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d150167 q = 1) (hb : d152706 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150167, d152706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150167, d152706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d150168 q = 1) (hb : d152707 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150168, d152707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150168, d152707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d150172 q = 1) (hb : d152709 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150172, d152709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150172, d152709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30024 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d22019 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d150173 q = 1) (hb : d152710 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150173, d152710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d150173, d152710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d150174 q = 1) (hb : d152711 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150174, d152711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d150174, d152711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d150175 q = 1) (hb : d152712 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150175, d152712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d150175, d152712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d150176 q = 1) (hb : d152713 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150176, d152713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d150176, d152713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d150182 q = 1) (hb : d152724 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150182, d152724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150182, d152724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30025 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d22204 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d150183 q = 1) (hb : d152725 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150183, d152725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d150183, d152725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d150184 q = 1) (hb : d152726 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150184, d152726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d150184, d152726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d150185 q = 1) (hb : d152727 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150185, d152727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d150185, d152727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d150186 q = 1) (hb : d152728 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150186, d152728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d150186, d152728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d150187 q = 1) (hb : d152729 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d150187, d152729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d150187, d152729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro30027 (p : Pattern) (ha : d150193 p = 1) (hb : d152735 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d150188 q = 1) (hb : d152730 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d150188, d152730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150188, d152730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30026 q ha hb
  have h2 (q : Pattern) (ha : d150189 q = 1) (hb : d152731 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d150189, d152731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150189, d152731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d150190 q = 1) (hb : d152732 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d150190, d152732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150190, d152732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d150191 q = 1) (hb : d152733 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d150191, d152733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150191, d152733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d150192 q = 1) (hb : d152734 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d150192, d152734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150192, d152734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d150193 q = 1) (hb : d152735 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d150193, d152735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150193, d152735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro30028 (p : Pattern) (ha : d150201 p = 1) (hb : d152139 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d22302 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d22311 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d22351 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d152134 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d150197 q = 1) (hb : d152135 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150197, d152135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d150197, d152135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d22435 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d150198 q = 1) (hb : d152136 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150198, d152136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150198, d152136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d150199 q = 1) (hb : d152137 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150199, d152137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d150199, d152137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d150200 q = 1) (hb : d152138 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150200, d152138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150200, d152138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d150201 q = 1) (hb : d152139 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150201, d152139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150201, d152139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro30029 (p : Pattern) (ha : d150206 p = 1) (hb : d152149 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d22302 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d22311 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d22351 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d152134 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d150197 q = 1) (hb : d152135 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150197, d152135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d150197, d152135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d22435 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d150198 q = 1) (hb : d152136 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150198, d152136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150198, d152136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d150199 q = 1) (hb : d152137 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150199, d152137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150199, d152137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d150200 q = 1) (hb : d152138 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150200, d152138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150200, d152138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d22445 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d22450 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d22453 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d152144 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d150202 q = 1) (hb : d152145 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150202, d152145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d150202, d152145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d22460 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d150203 q = 1) (hb : d152146 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150203, d152146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d150203, d152146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d150204 q = 1) (hb : d152147 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150204, d152147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d150204, d152147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d150205 q = 1) (hb : d152148 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150205, d152148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d150205, d152148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d150206 q = 1) (hb : d152149 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150206, d152149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d150206, d152149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro30030 (p : Pattern) (ha : d150213 p = 1) (hb : d152741 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d22453 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d152144 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d150202 q = 1) (hb : d152145 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150202, d152145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150202, d152145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d22460 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d150203 q = 1) (hb : d152146 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150203, d152146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150203, d152146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d150211 q = 1) (hb : d152147 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150211, d152147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150211, d152147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d150212 q = 1) (hb : d152148 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150212, d152148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150212, d152148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d150213 q = 1) (hb : d152741 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150213, d152741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150213, d152741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro30031 (p : Pattern) (ha : d150223 p = 1) (hb : d152756 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d22575 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d152751 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d150219 q = 1) (hb : d152752 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150219, d152752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150219, d152752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d22653 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d150220 q = 1) (hb : d152753 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150220, d152753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150220, d152753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d150221 q = 1) (hb : d152754 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150221, d152754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150221, d152754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d150222 q = 1) (hb : d152755 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150222, d152755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150222, d152755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d150223 q = 1) (hb : d152756 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150223, d152756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150223, d152756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro30032 (p : Pattern) (ha : d150229 p = 1) (hb : d152762 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d22294 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d150207 q = 1) (hb : d152150 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150207, d152150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30028 q ha hb
    | true =>
      simp only [d150207, d152150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30029 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d22483 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d150208 q = 1) (hb : d152151 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150208, d152151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150208, d152151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d150209 q = 1) (hb : d152739 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150209, d152739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150209, d152739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d150210 q = 1) (hb : d152740 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150210, d152740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150210, d152740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d150214 q = 1) (hb : d152742 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150214, d152742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150214, d152742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30030 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d22492 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d150215 q = 1) (hb : d152743 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150215, d152743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d150215, d152743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d150216 q = 1) (hb : d152744 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150216, d152744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d150216, d152744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d150217 q = 1) (hb : d152745 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150217, d152745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d150217, d152745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d150218 q = 1) (hb : d152746 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150218, d152746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d150218, d152746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d150224 q = 1) (hb : d152757 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150224, d152757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150224, d152757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30031 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d22669 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d150225 q = 1) (hb : d152758 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150225, d152758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d150225, d152758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d150226 q = 1) (hb : d152759 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150226, d152759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d150226, d152759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d150227 q = 1) (hb : d152760 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150227, d152760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d150227, d152760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d150228 q = 1) (hb : d152761 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150228, d152761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d150228, d152761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d150229 q = 1) (hb : d152762 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d150229, d152762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d150229, d152762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro30033 (p : Pattern) (ha : d150235 p = 1) (hb : d152768 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d150230 q = 1) (hb : d152763 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d150230, d152763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150230, d152763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30032 q ha hb
  have h2 (q : Pattern) (ha : d150231 q = 1) (hb : d152764 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d150231, d152764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150231, d152764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d150232 q = 1) (hb : d152765 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d150232, d152765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150232, d152765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d150233 q = 1) (hb : d152766 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d150233, d152766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150233, d152766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d150234 q = 1) (hb : d152767 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d150234, d152767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150234, d152767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d150235 q = 1) (hb : d152768 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d150235, d152768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150235, d152768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro30034 (p : Pattern) (ha : d150244 p = 1) (hb : d152378 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d22757 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d22766 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d22794 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d152373 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d150240 q = 1) (hb : d152374 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150240, d152374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d150240, d152374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d22868 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d150241 q = 1) (hb : d152375 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150241, d152375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150241, d152375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d150242 q = 1) (hb : d152376 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150242, d152376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d150242, d152376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d150243 q = 1) (hb : d152377 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150243, d152377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150243, d152377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d150244 q = 1) (hb : d152378 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150244, d152378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150244, d152378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro30035 (p : Pattern) (ha : d150249 p = 1) (hb : d152388 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d22757 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d22766 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d22794 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d152373 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d150240 q = 1) (hb : d152374 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150240, d152374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d150240, d152374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d22868 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d150241 q = 1) (hb : d152375 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150241, d152375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150241, d152375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d150242 q = 1) (hb : d152376 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150242, d152376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150242, d152376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d150243 q = 1) (hb : d152377 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150243, d152377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150243, d152377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d22878 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d22883 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d22886 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d152383 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d150245 q = 1) (hb : d152384 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150245, d152384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d150245, d152384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d22893 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d150246 q = 1) (hb : d152385 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150246, d152385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d150246, d152385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d150247 q = 1) (hb : d152386 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150247, d152386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d150247, d152386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d150248 q = 1) (hb : d152387 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150248, d152387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d150248, d152387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d150249 q = 1) (hb : d152388 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150249, d152388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d150249, d152388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro30036 (p : Pattern) (ha : d150256 p = 1) (hb : d152775 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d22886 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d152383 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d150245 q = 1) (hb : d152384 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150245, d152384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150245, d152384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d22893 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d150246 q = 1) (hb : d152385 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150246, d152385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150246, d152385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d150254 q = 1) (hb : d152386 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150254, d152386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150254, d152386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d150255 q = 1) (hb : d152387 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150255, d152387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150255, d152387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d150256 q = 1) (hb : d152775 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150256, d152775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150256, d152775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro30037 (p : Pattern) (ha : d150266 p = 1) (hb : d152790 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d22989 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d152785 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d150262 q = 1) (hb : d152786 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150262, d152786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150262, d152786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d23059 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d150263 q = 1) (hb : d152787 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150263, d152787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150263, d152787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d150264 q = 1) (hb : d152788 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150264, d152788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150264, d152788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d150265 q = 1) (hb : d152789 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150265, d152789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150265, d152789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d150266 q = 1) (hb : d152790 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150266, d152790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150266, d152790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro30038 (p : Pattern) (ha : d150272 p = 1) (hb : d152796 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d22749 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d150250 q = 1) (hb : d152389 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150250, d152389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30034 q ha hb
    | true =>
      simp only [d150250, d152389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30035 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d22916 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d150251 q = 1) (hb : d152390 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150251, d152390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150251, d152390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d150252 q = 1) (hb : d152773 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150252, d152773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150252, d152773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d150253 q = 1) (hb : d152774 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150253, d152774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150253, d152774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d150257 q = 1) (hb : d152776 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150257, d152776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150257, d152776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30036 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d22925 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d150258 q = 1) (hb : d152777 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150258, d152777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d150258, d152777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d150259 q = 1) (hb : d152778 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150259, d152778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d150259, d152778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d150260 q = 1) (hb : d152779 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150260, d152779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d150260, d152779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d150261 q = 1) (hb : d152780 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150261, d152780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d150261, d152780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d150267 q = 1) (hb : d152791 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150267, d152791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150267, d152791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30037 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d23075 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d150268 q = 1) (hb : d152792 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150268, d152792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d150268, d152792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d150269 q = 1) (hb : d152793 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150269, d152793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d150269, d152793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d150270 q = 1) (hb : d152794 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150270, d152794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d150270, d152794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d150271 q = 1) (hb : d152795 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150271, d152795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d150271, d152795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d150272 q = 1) (hb : d152796 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d150272, d152796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d150272, d152796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro30039 (p : Pattern) (ha : d150278 p = 1) (hb : d152802 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d150273 q = 1) (hb : d152797 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d150273, d152797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150273, d152797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30038 q ha hb
  have h2 (q : Pattern) (ha : d150274 q = 1) (hb : d152798 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d150274, d152798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150274, d152798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d150275 q = 1) (hb : d152799 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d150275, d152799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150275, d152799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d150276 q = 1) (hb : d152800 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d150276, d152800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150276, d152800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d150277 q = 1) (hb : d152801 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d150277, d152801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150277, d152801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d150278 q = 1) (hb : d152802 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d150278, d152802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150278, d152802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro30040 (p : Pattern) (ha : d150284 p = 1) (hb : d152808 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d150113 q = 1) (hb : d152677 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d150113, d152677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30009 q ha hb
    | true =>
      simp only [d150113, d152677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30015 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d150153 q = 1) (hb : d152704 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d150153, d152704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150153, d152704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30021 q ha hb
  have h3 (q : Pattern) (ha : d150154 q = 1) (hb : d152705 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d150154, d152705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150154, d152705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d150194 q = 1) (hb : d152736 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d150194, d152736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150194, d152736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30027 q ha hb
  have h5 (q : Pattern) (ha : d150195 q = 1) (hb : d152737 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d150195, d152737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150195, d152737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d150196 q = 1) (hb : d152738 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d150196, d152738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150196, d152738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d150236 q = 1) (hb : d152769 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d150236, d152769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150236, d152769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30033 q ha hb
  have h8 (q : Pattern) (ha : d150237 q = 1) (hb : d152770 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d150237, d152770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150237, d152770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d150238 q = 1) (hb : d152771 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d150238, d152771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150238, d152771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d150239 q = 1) (hb : d152772 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d150239, d152772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d150239, d152772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d150279 q = 1) (hb : d152803 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d150279, d152803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150279, d152803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30039 q ha hb
  have h12 (q : Pattern) (ha : d150280 q = 1) (hb : d152804 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d150280, d152804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150280, d152804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d150281 q = 1) (hb : d152805 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d150281, d152805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150281, d152805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d150282 q = 1) (hb : d152806 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d150282, d152806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150282, d152806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d150283 q = 1) (hb : d152807 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d150283, d152807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d150283, d152807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d150284 q = 1) (hb : d152808 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d150284, d152808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d150284, d152808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro30041 (p : Pattern) (ha : d150290 p = 1) (hb : d152814 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d150285 q = 1) (hb : d152809 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d150285, d152809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30040 q ha hb
    | true =>
      simp only [d150285, d152809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d150286 q = 1) (hb : d152810 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d150286, d152810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150286, d152810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d150287 q = 1) (hb : d152811 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d150287, d152811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150287, d152811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d150288 q = 1) (hb : d152812 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d150288, d152812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150288, d152812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d150289 q = 1) (hb : d152813 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d150289, d152813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150289, d152813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d150290 q = 1) (hb : d152814 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d150290, d152814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150290, d152814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro30042 (p : Pattern) (ha : d150296 p = 1) (hb : d152820 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d150291 q = 1) (hb : d152815 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d150291, d152815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30041 q ha hb
    | true =>
      simp only [d150291, d152815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d150292 q = 1) (hb : d152816 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d150292, d152816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150292, d152816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d150293 q = 1) (hb : d152817 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d150293, d152817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150293, d152817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d150294 q = 1) (hb : d152818 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d150294, d152818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150294, d152818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d150295 q = 1) (hb : d152819 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d150295, d152819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150295, d152819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d150296 q = 1) (hb : d152820 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d150296, d152820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150296, d152820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro30043 (p : Pattern) (ha : d150302 p = 1) (hb : d152826 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d150297 q = 1) (hb : d152821 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d150297, d152821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30042 q ha hb
    | true =>
      simp only [d150297, d152821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d150298 q = 1) (hb : d152822 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d150298, d152822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150298, d152822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d150299 q = 1) (hb : d152823 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d150299, d152823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150299, d152823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d150300 q = 1) (hb : d152824 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d150300, d152824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150300, d152824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d150301 q = 1) (hb : d152825 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d150301, d152825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150301, d152825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d150302 q = 1) (hb : d152826 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d150302, d152826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150302, d152826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro30044 (p : Pattern) (ha : d150308 p = 1) (hb : d152832 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d150303 q = 1) (hb : d152827 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d150303, d152827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30043 q ha hb
    | true =>
      simp only [d150303, d152827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d150304 q = 1) (hb : d152828 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d150304, d152828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150304, d152828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d150305 q = 1) (hb : d152829 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d150305, d152829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150305, d152829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d150306 q = 1) (hb : d152830 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d150306, d152830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150306, d152830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d150307 q = 1) (hb : d152831 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d150307, d152831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150307, d152831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d150308 q = 1) (hb : d152832 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d150308, d152832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150308, d152832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro30045 (p : Pattern) (ha : d150314 p = 1) (hb : d152838 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d150309 q = 1) (hb : d152833 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d150309, d152833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30044 q ha hb
    | true =>
      simp only [d150309, d152833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d150310 q = 1) (hb : d152834 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d150310, d152834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150310, d152834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d150311 q = 1) (hb : d152835 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d150311, d152835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150311, d152835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d150312 q = 1) (hb : d152836 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d150312, d152836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150312, d152836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d150313 q = 1) (hb : d152837 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d150313, d152837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150313, d152837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d150314 q = 1) (hb : d152838 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d150314, d152838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150314, d152838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro30046 (p : Pattern) (ha : d150320 p = 1) (hb : d152844 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d150315 q = 1) (hb : d152839 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d150315, d152839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30045 q ha hb
    | true =>
      simp only [d150315, d152839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d150316 q = 1) (hb : d152840 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d150316, d152840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150316, d152840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d150317 q = 1) (hb : d152841 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d150317, d152841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150317, d152841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d150318 q = 1) (hb : d152842 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d150318, d152842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150318, d152842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d150319 q = 1) (hb : d152843 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d150319, d152843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150319, d152843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d150320 q = 1) (hb : d152844 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d150320, d152844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150320, d152844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro30047 (p : Pattern) (ha : d150326 p = 1) (hb : d152850 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d150321 q = 1) (hb : d152845 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d150321, d152845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30046 q ha hb
    | true =>
      simp only [d150321, d152845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d150322 q = 1) (hb : d152846 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d150322, d152846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150322, d152846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d150323 q = 1) (hb : d152847 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d150323, d152847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150323, d152847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d150324 q = 1) (hb : d152848 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d150324, d152848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150324, d152848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d150325 q = 1) (hb : d152849 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d150325, d152849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150325, d152849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d150326 q = 1) (hb : d152850 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d150326, d152850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150326, d152850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro30048 (p : Pattern) (ha : d24 p = 1) (hb : d152854 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d23 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d152852 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d24 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d24, d152854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d24, d152854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro30049 (p : Pattern) (ha : d30 p = 1) (hb : d152855 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30048 q ha hb
    | true =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d26 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d27 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d27, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d28 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d28, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d28, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d29 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d29, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d29, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d30 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d30, d152855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d30, d152855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro30050 (p : Pattern) (ha : d36 p = 1) (hb : d152855 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30049 q ha hb
    | true =>
      simp only [d31, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d32 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d32, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d34 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d34, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d34, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d35 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d35, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d35, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d36 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d36, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d36, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro30051 (p : Pattern) (ha : d42 p = 1) (hb : d152855 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d37 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30050 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d38 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d40 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d40, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d40, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d41 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d41, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d41, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d42 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d42, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro30052 (p : Pattern) (ha : d48 p = 1) (hb : d152855 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d43 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30051 q ha hb
    | true =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d44 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d45 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d45, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d46 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d47 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d47, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d47, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d48 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d48, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d48, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro30053 (p : Pattern) (ha : d49 p = 1) (hb : d152855 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d37 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30050 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d38 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d40 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d40, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d40, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d41 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d41, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d41, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d49 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d49, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d49, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro30054 (p : Pattern) (ha : d55 p = 1) (hb : d152855 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d43 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30051 q ha hb
    | true =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d44 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d45 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d45, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d46 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d47 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d47, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d47, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d50 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30053 q ha hb
    | true =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d51 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d52 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d52, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d52, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d53 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d54 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d54, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d55 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d55, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d55, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro30055 (p : Pattern) (ha : d60 p = 1) (hb : d152855 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d50 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30053 q ha hb
    | true =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d51 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d52 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d52, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d52, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d54, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d60 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d60, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d60, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro30056 (p : Pattern) (ha : d71 p = 1) (hb : d152855 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d66 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d66, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d66, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30048 q ha hb
  have h2 (q : Pattern) (ha : d25 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30048 q ha hb
    | true =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d67 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d67, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d67, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d26 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d68 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d68, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d68, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d69 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d69, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d69, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d70 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d70, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d70, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d71 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d71, d152855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d71, d152855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro30057 (p : Pattern) (ha : d77 p = 1) (hb : d152855 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d72 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d72, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30056 q ha hb
    | true =>
      simp only [d72, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d73 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d73, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d73, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d74 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d74, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d75 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d75, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d75, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d76 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d76, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d76, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d77 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d77, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d77, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro30058 (p : Pattern) (ha : d83 p = 1) (hb : d152855 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d78 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d78, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30057 q ha hb
    | true =>
      simp only [d78, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d79 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d79, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d79, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d80 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d80, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d80, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d81 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d81, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d81, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d82 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d82, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d82, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d83 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d83, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d83, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro30059 (p : Pattern) (ha : d89 p = 1) (hb : d152855 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30058 q ha hb
    | true =>
      simp only [d84, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d85 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d86 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d86, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d86, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d87 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d87, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d87, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d88 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d88, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d89 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d89, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro30060 (p : Pattern) (ha : d95 p = 1) (hb : d152855 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d56 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d56, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30052 q ha hb
    | true =>
      simp only [d56, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30054 q ha hb
  have h2 (q : Pattern) (ha : d57 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d57, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d57, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d58 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d58, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d58, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d59 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d59, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d59, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d61 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d61, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30055 q ha hb
  have h6 (q : Pattern) (ha : d62 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d62, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d63 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d63, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d63, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d64 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d64, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d64, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d65 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d65, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d65, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d90 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d90, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d90, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30059 q ha hb
  have h11 (q : Pattern) (ha : d91 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d91, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d91, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d92 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d92, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d92, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d93 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d93, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d93, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d94 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d94, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d95 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d95, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d95, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro30061 (p : Pattern) (ha : d104 p = 1) (hb : d152855 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d43 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30051 q ha hb
    | true =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d100 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d101 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d102 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d103 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d104 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro30062 (p : Pattern) (ha : d111 p = 1) (hb : d152855 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d43 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30051 q ha hb
    | true =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d100 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d101 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d102 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d103 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d50 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30053 q ha hb
    | true =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d107 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d109 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d110 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d111 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro30063 (p : Pattern) (ha : d213 p = 1) (hb : d152855 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d43 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30051 q ha hb
    | true =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d100 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d101 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d102 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d103 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d213 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro30064 (p : Pattern) (ha : d116 p = 1) (hb : d152855 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d37 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30050 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d38 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d40 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d40, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d40, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d115 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d116 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro30065 (p : Pattern) (ha : d123 p = 1) (hb : d152855 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d37 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30050 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d38 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d121 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d123 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro30066 (p : Pattern) (ha : d138 p = 1) (hb : d152854 p = 1) : d156536 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d137 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23 q = 1) (hb : d152852 q = 1) : d23 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d138 q = 1) (hb : d152854 q = 1) : d156536 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d138, d152854, d156536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d138, d152854, d156536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro30067 (p : Pattern) (ha : d4818 p = 1) (hb : d152855 p = 1) : d156542 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d139 q = 1) (hb : d152854 q = 1) : d156537 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d139, d156537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30066 q ha hb
    | true =>
      simp only [d139, d156537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d140 q = 1) (hb : d152854 q = 1) : d156538 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d140, d156538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d140, d156538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d141 q = 1) (hb : d152854 q = 1) : d156539 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d141, d156539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d141, d156539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d142 q = 1) (hb : d152854 q = 1) : d156540 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d142, d156540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d142, d156540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30048 q ha hb
    | true =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d26 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d27 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d27, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d28 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d28, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d28, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d143 q = 1) (hb : d152854 q = 1) : d156541 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d143, d156541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d143, d156541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d4818 q = 1) (hb : d152855 q = 1) : d156542 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d4818, d152855, d156542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d4818, d152855, d156542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro30068 (p : Pattern) (ha : d12227 p = 1) (hb : d152855 p = 1) : d156548 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4819 q = 1) (hb : d152855 q = 1) : d156543 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d4819, d156543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30067 q ha hb
    | true =>
      simp only [d4819, d156543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30049 q ha hb
  have h2 (q : Pattern) (ha : d4820 q = 1) (hb : d152855 q = 1) : d156544 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d4820, d156544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4820, d156544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d4821 q = 1) (hb : d152855 q = 1) : d156545 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d4821, d156545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4821, d156545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d31 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30049 q ha hb
    | true =>
      simp only [d31, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d32 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d32, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12225 q = 1) (hb : d152855 q = 1) : d156546 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12225, d156546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12225, d156546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d34 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d34, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d34, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d12226 q = 1) (hb : d152855 q = 1) : d156547 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12226, d156547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12226, d156547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d12227 q = 1) (hb : d152855 q = 1) : d156548 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12227, d156548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d12227, d156548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro30069 (p : Pattern) (ha : d12233 p = 1) (hb : d152855 p = 1) : d156554 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12228 q = 1) (hb : d152855 q = 1) : d156549 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12228, d156549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30068 q ha hb
    | true =>
      simp only [d12228, d156549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12229 q = 1) (hb : d152855 q = 1) : d156550 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12229, d156550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12229, d156550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30050 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12230 q = 1) (hb : d152855 q = 1) : d156551 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12230, d156551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12230, d156551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12231 q = 1) (hb : d152855 q = 1) : d156552 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12231, d156552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12231, d156552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12232 q = 1) (hb : d152855 q = 1) : d156553 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12232, d156553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12232, d156553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12233 q = 1) (hb : d152855 q = 1) : d156554 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12233, d156554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12233, d156554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro30070 (p : Pattern) (ha : d115242 p = 1) (hb : d152855 p = 1) : d156560 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d117 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30064 q ha hb
    | true =>
      simp only [d117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d118 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d120 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d124 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30065 q ha hb
    | true =>
      simp only [d124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d125 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d126 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12234 q = 1) (hb : d152855 q = 1) : d156555 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12234, d156555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30069 q ha hb
    | true =>
      simp only [d12234, d156555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30051 q ha hb
  have h9 (q : Pattern) (ha : d115238 q = 1) (hb : d152855 q = 1) : d156556 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115238, d156556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d115238, d156556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d43 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30051 q ha hb
    | true =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d44 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d115239 q = 1) (hb : d152855 q = 1) : d156557 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115239, d156557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d115239, d156557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d115240 q = 1) (hb : d152855 q = 1) : d156558 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115240, d156558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d115240, d156558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d115241 q = 1) (hb : d152855 q = 1) : d156559 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115241, d156559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115241, d156559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d115242 q = 1) (hb : d152855 q = 1) : d156560 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115242, d156560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115242, d156560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro30071 (p : Pattern) (ha : d194 p = 1) (hb : d152855 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d37 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30050 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d38 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d40 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d40, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d40, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d115 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d194 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro30072 (p : Pattern) (ha : d199 p = 1) (hb : d152855 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d37 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30050 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d38 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d121 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d199 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro30073 (p : Pattern) (ha : d12240 p = 1) (hb : d152855 p = 1) : d156561 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12228 q = 1) (hb : d152855 q = 1) : d156549 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12228, d156549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30068 q ha hb
    | true =>
      simp only [d12228, d156549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12229 q = 1) (hb : d152855 q = 1) : d156550 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12229, d156550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12229, d156550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30050 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12230 q = 1) (hb : d152855 q = 1) : d156551 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12230, d156551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12230, d156551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12231 q = 1) (hb : d152855 q = 1) : d156552 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12231, d156552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12231, d156552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12232 q = 1) (hb : d152855 q = 1) : d156553 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12232, d156553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12232, d156553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12240 q = 1) (hb : d152855 q = 1) : d156561 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12240, d156561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12240, d156561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro30074 (p : Pattern) (ha : d115247 p = 1) (hb : d152855 p = 1) : d156567 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d117 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30064 q ha hb
    | true =>
      simp only [d117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d118 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d120 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d124 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30065 q ha hb
    | true =>
      simp only [d124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d125 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d126 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12234 q = 1) (hb : d152855 q = 1) : d156555 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12234, d156555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30069 q ha hb
    | true =>
      simp only [d12234, d156555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30051 q ha hb
  have h9 (q : Pattern) (ha : d115238 q = 1) (hb : d152855 q = 1) : d156556 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115238, d156556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d115238, d156556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d43 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30051 q ha hb
    | true =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d44 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d115239 q = 1) (hb : d152855 q = 1) : d156557 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115239, d156557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d115239, d156557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d115240 q = 1) (hb : d152855 q = 1) : d156558 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115240, d156558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d115240, d156558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d115241 q = 1) (hb : d152855 q = 1) : d156559 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115241, d156559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115241, d156559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d195 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30071 q ha hb
    | true =>
      simp only [d195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d196 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d197 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d198 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d200 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30072 q ha hb
    | true =>
      simp only [d200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d201 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d202 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d12241 q = 1) (hb : d152855 q = 1) : d156562 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12241, d156562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30073 q ha hb
    | true =>
      simp only [d12241, d156562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30053 q ha hb
  have h23 (q : Pattern) (ha : d115243 q = 1) (hb : d152855 q = 1) : d156563 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115243, d156563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d115243, d156563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d50 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30053 q ha hb
    | true =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d51 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d115244 q = 1) (hb : d152855 q = 1) : d156564 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115244, d156564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d115244, d156564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d115245 q = 1) (hb : d152855 q = 1) : d156565 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115245, d156565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d115245, d156565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d115246 q = 1) (hb : d152855 q = 1) : d156566 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115246, d156566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d115246, d156566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d115247 q = 1) (hb : d152855 q = 1) : d156567 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115247, d156567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d115247, d156567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro30075 (p : Pattern) (ha : d115254 p = 1) (hb : d152855 p = 1) : d156572 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12241 q = 1) (hb : d152855 q = 1) : d156562 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12241, d156562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30073 q ha hb
    | true =>
      simp only [d12241, d156562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30053 q ha hb
  have h2 (q : Pattern) (ha : d115243 q = 1) (hb : d152855 q = 1) : d156563 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115243, d156563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115243, d156563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d50 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30053 q ha hb
    | true =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d51 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d115244 q = 1) (hb : d152855 q = 1) : d156564 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115244, d156564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115244, d156564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115252 q = 1) (hb : d152855 q = 1) : d156565 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115252, d156565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115252, d156565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d115253 q = 1) (hb : d152855 q = 1) : d156566 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115253, d156566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115253, d156566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d115254 q = 1) (hb : d152855 q = 1) : d156572 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115254, d156572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115254, d156572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro30076 (p : Pattern) (ha : d6078 p = 1) (hb : d152855 p = 1) : d156583 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d226 q = 1) (hb : d152854 q = 1) : d156578 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d226, d156578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d226, d156578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30066 q ha hb
  have h2 (q : Pattern) (ha : d139 q = 1) (hb : d152854 q = 1) : d156537 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d139, d156537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30066 q ha hb
    | true =>
      simp only [d139, d156537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d227 q = 1) (hb : d152854 q = 1) : d156579 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d227, d156579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d227, d156579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d140 q = 1) (hb : d152854 q = 1) : d156538 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d140, d156538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d140, d156538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d228 q = 1) (hb : d152854 q = 1) : d156580 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d228, d156580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d228, d156580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d229 q = 1) (hb : d152854 q = 1) : d156581 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d229, d156581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d229, d156581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d66 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d66, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d66, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30048 q ha hb
  have h8 (q : Pattern) (ha : d25 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30048 q ha hb
    | true =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d67 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d67, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d67, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d26 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d68 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d68, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d68, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d69 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d69, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d69, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d230 q = 1) (hb : d152854 q = 1) : d156582 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d230, d156582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d230, d156582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d6078 q = 1) (hb : d152855 q = 1) : d156583 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d6078, d152855, d156583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d6078, d152855, d156583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro30077 (p : Pattern) (ha : d12261 p = 1) (hb : d152855 p = 1) : d156589 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6079 q = 1) (hb : d152855 q = 1) : d156584 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d6079, d156584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30076 q ha hb
    | true =>
      simp only [d6079, d156584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30056 q ha hb
  have h2 (q : Pattern) (ha : d6080 q = 1) (hb : d152855 q = 1) : d156585 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d6080, d156585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6080, d156585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6081 q = 1) (hb : d152855 q = 1) : d156586 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d6081, d156586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6081, d156586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d72 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d72, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30056 q ha hb
    | true =>
      simp only [d72, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d73 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d73, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d73, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d74, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12259 q = 1) (hb : d152855 q = 1) : d156587 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12259, d156587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12259, d156587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d75 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d75, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d75, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d12260 q = 1) (hb : d152855 q = 1) : d156588 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12260, d156588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12260, d156588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d12261 q = 1) (hb : d152855 q = 1) : d156589 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12261, d156589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d12261, d156589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro30078 (p : Pattern) (ha : d12267 p = 1) (hb : d152855 p = 1) : d156595 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12262 q = 1) (hb : d152855 q = 1) : d156590 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12262, d156590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30077 q ha hb
    | true =>
      simp only [d12262, d156590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12263 q = 1) (hb : d152855 q = 1) : d156591 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12263, d156591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12263, d156591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d78 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d78, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30057 q ha hb
    | true =>
      simp only [d78, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d79 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d79, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d79, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12264 q = 1) (hb : d152855 q = 1) : d156592 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12264, d156592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12264, d156592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12265 q = 1) (hb : d152855 q = 1) : d156593 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12265, d156593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12265, d156593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12266 q = 1) (hb : d152855 q = 1) : d156594 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12266, d156594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12266, d156594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12267 q = 1) (hb : d152855 q = 1) : d156595 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12267, d156595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12267, d156595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro30079 (p : Pattern) (ha : d115264 p = 1) (hb : d152855 p = 1) : d156601 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12268 q = 1) (hb : d152855 q = 1) : d156596 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12268, d156596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30078 q ha hb
    | true =>
      simp only [d12268, d156596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30058 q ha hb
  have h2 (q : Pattern) (ha : d115260 q = 1) (hb : d152855 q = 1) : d156597 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115260, d156597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115260, d156597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d84 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30058 q ha hb
    | true =>
      simp only [d84, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d85 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d115261 q = 1) (hb : d152855 q = 1) : d156598 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115261, d156598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115261, d156598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115262 q = 1) (hb : d152855 q = 1) : d156599 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115262, d156599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115262, d156599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d115263 q = 1) (hb : d152855 q = 1) : d156600 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115263, d156600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115263, d156600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d115264 q = 1) (hb : d152855 q = 1) : d156601 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115264, d156601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115264, d156601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro30080 (p : Pattern) (ha : d115270 p = 1) (hb : d152855 p = 1) : d156607 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d105 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30061 q ha hb
  have h2 (q : Pattern) (ha : d106 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d112 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30061 q ha hb
    | true =>
      simp only [d112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30062 q ha hb
  have h4 (q : Pattern) (ha : d113 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d114 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115248 q = 1) (hb : d152855 q = 1) : d156568 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115248, d156568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30070 q ha hb
    | true =>
      simp only [d115248, d156568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30074 q ha hb
  have h7 (q : Pattern) (ha : d214 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30063 q ha hb
    | true =>
      simp only [d214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d115249 q = 1) (hb : d152855 q = 1) : d156569 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115249, d156569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d115249, d156569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d115250 q = 1) (hb : d152855 q = 1) : d156570 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115250, d156570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d115250, d156570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d115251 q = 1) (hb : d152855 q = 1) : d156571 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115251, d156571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d115251, d156571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d115255 q = 1) (hb : d152855 q = 1) : d156573 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115255, d156573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115255, d156573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30075 q ha hb
  have h12 (q : Pattern) (ha : d115256 q = 1) (hb : d152855 q = 1) : d156574 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115256, d156574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d115256, d156574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d115257 q = 1) (hb : d152855 q = 1) : d156575 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115257, d156575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d115257, d156575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d115258 q = 1) (hb : d152855 q = 1) : d156576 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115258, d156576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d115258, d156576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d115259 q = 1) (hb : d152855 q = 1) : d156577 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d115259, d156577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d115259, d156577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d115265 q = 1) (hb : d152855 q = 1) : d156602 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115265, d156602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115265, d156602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30079 q ha hb
  have h17 (q : Pattern) (ha : d115266 q = 1) (hb : d152855 q = 1) : d156603 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115266, d156603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d115266, d156603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d115267 q = 1) (hb : d152855 q = 1) : d156604 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115267, d156604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d115267, d156604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d115268 q = 1) (hb : d152855 q = 1) : d156605 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115268, d156605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d115268, d156605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d115269 q = 1) (hb : d152855 q = 1) : d156606 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d115269, d156606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d115269, d156606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d115270 q = 1) (hb : d152855 q = 1) : d156607 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d115270, d156607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d115270, d156607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro30081 (p : Pattern) (ha : d406 p = 1) (hb : d152855 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d50 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30053 q ha hb
    | true =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d107 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d109 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d110 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d406 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro30082 (p : Pattern) (ha : d462 p = 1) (hb : d152855 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30058 q ha hb
    | true =>
      simp only [d84, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d458 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d459 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d460 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d461 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d462 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro30083 (p : Pattern) (ha : d12289 p = 1) (hb : d152855 p = 1) : d156617 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12234 q = 1) (hb : d152855 q = 1) : d156555 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12234, d156555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30069 q ha hb
    | true =>
      simp only [d12234, d156555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30051 q ha hb
  have h2 (q : Pattern) (ha : d12285 q = 1) (hb : d152855 q = 1) : d156613 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12285, d156613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12285, d156613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12286 q = 1) (hb : d152855 q = 1) : d156614 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12286, d156614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12286, d156614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12287 q = 1) (hb : d152855 q = 1) : d156615 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12287, d156615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12287, d156615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12288 q = 1) (hb : d152855 q = 1) : d156616 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12288, d156616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12288, d156616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12289 q = 1) (hb : d152855 q = 1) : d156617 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d12289, d156617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12289, d156617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro30084 (p : Pattern) (ha : d12296 p = 1) (hb : d152855 p = 1) : d156624 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12234 q = 1) (hb : d152855 q = 1) : d156555 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12234, d156555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30069 q ha hb
    | true =>
      simp only [d12234, d156555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30051 q ha hb
  have h2 (q : Pattern) (ha : d12285 q = 1) (hb : d152855 q = 1) : d156613 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12285, d156613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12285, d156613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12286 q = 1) (hb : d152855 q = 1) : d156614 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12286, d156614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12286, d156614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12287 q = 1) (hb : d152855 q = 1) : d156615 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12287, d156615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12287, d156615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12288 q = 1) (hb : d152855 q = 1) : d156616 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12288, d156616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12288, d156616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12241 q = 1) (hb : d152855 q = 1) : d156562 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12241, d156562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30073 q ha hb
    | true =>
      simp only [d12241, d156562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30053 q ha hb
  have h7 (q : Pattern) (ha : d12292 q = 1) (hb : d152855 q = 1) : d156620 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12292, d156620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12292, d156620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12293 q = 1) (hb : d152855 q = 1) : d156621 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12293, d156621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12293, d156621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d12294 q = 1) (hb : d152855 q = 1) : d156622 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12294, d156622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12294, d156622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d12295 q = 1) (hb : d152855 q = 1) : d156623 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12295, d156623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12295, d156623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d12296 q = 1) (hb : d152855 q = 1) : d156624 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d12296, d156624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12296, d156624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro30085 (p : Pattern) (ha : d12373 p = 1) (hb : d152855 p = 1) : d156682 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12234 q = 1) (hb : d152855 q = 1) : d156555 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12234, d156555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30069 q ha hb
    | true =>
      simp only [d12234, d156555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30051 q ha hb
  have h2 (q : Pattern) (ha : d12285 q = 1) (hb : d152855 q = 1) : d156613 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12285, d156613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12285, d156613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12286 q = 1) (hb : d152855 q = 1) : d156614 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12286, d156614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12286, d156614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12287 q = 1) (hb : d152855 q = 1) : d156615 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12287, d156615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12287, d156615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12288 q = 1) (hb : d152855 q = 1) : d156616 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12288, d156616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12288, d156616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d43 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30051 q ha hb
    | true =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d100 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d101 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d102 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d103 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d12373 q = 1) (hb : d152855 q = 1) : d156682 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d12373, d156682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12373, d156682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro30086 (p : Pattern) (ha : d12301 p = 1) (hb : d152855 p = 1) : d156629 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12228 q = 1) (hb : d152855 q = 1) : d156549 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12228, d156549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30068 q ha hb
    | true =>
      simp only [d12228, d156549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12229 q = 1) (hb : d152855 q = 1) : d156550 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12229, d156550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12229, d156550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30050 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12230 q = 1) (hb : d152855 q = 1) : d156551 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12230, d156551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12230, d156551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12231 q = 1) (hb : d152855 q = 1) : d156552 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12231, d156552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12231, d156552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12300 q = 1) (hb : d152855 q = 1) : d156628 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12300, d156628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12300, d156628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12301 q = 1) (hb : d152855 q = 1) : d156629 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12301, d156629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12301, d156629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro30087 (p : Pattern) (ha : d12308 p = 1) (hb : d152855 p = 1) : d156636 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12228 q = 1) (hb : d152855 q = 1) : d156549 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12228, d156549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30068 q ha hb
    | true =>
      simp only [d12228, d156549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12229 q = 1) (hb : d152855 q = 1) : d156550 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12229, d156550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12229, d156550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30050 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12230 q = 1) (hb : d152855 q = 1) : d156551 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12230, d156551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12230, d156551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12306 q = 1) (hb : d152855 q = 1) : d156634 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12306, d156634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12306, d156634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12307 q = 1) (hb : d152855 q = 1) : d156635 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12307, d156635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12307, d156635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12308 q = 1) (hb : d152855 q = 1) : d156636 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12308, d156636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12308, d156636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro30088 (p : Pattern) (ha : d318 p = 1) (hb : d152854 p = 1) : d156640 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d317 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d134 q = 1) : d134 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d20 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d135 q = 1) (hb : d152852 q = 1) : d9796 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d135, d152852, d9796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d135, d152852, d9796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d21 q = 1) (hb : d152852 q = 1) : d21 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d136 q = 1) (hb : d152852 q = 1) : d25102 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d136, d25102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d136, d25102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d152852 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d137 q = 1) (hb : d152852 q = 1) : d25103 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d137, d25103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d137, d25103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d318 q = 1) (hb : d152854 q = 1) : d156640 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d318, d152854, d156640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d318, d152854, d156640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro30089 (p : Pattern) (ha : d12312 p = 1) (hb : d152855 p = 1) : d156646 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d319 q = 1) (hb : d152854 q = 1) : d156641 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319, d156641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30088 q ha hb
    | true =>
      simp only [d319, d156641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d320 q = 1) (hb : d152854 q = 1) : d156642 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d320, d156642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d320, d156642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d321 q = 1) (hb : d152854 q = 1) : d156643 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d321, d156643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d321, d156643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d322 q = 1) (hb : d152854 q = 1) : d156644 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d322, d156644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d322, d156644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d139 q = 1) (hb : d152854 q = 1) : d156537 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d139, d156537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30066 q ha hb
    | true =>
      simp only [d139, d156537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d140 q = 1) (hb : d152854 q = 1) : d156538 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d140, d156538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d140, d156538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d141 q = 1) (hb : d152854 q = 1) : d156539 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d141, d156539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d141, d156539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d142 q = 1) (hb : d152854 q = 1) : d156540 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d142, d156540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d142, d156540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d323 q = 1) (hb : d152854 q = 1) : d156645 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d323, d156645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d323, d156645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d12312 q = 1) (hb : d152855 q = 1) : d156646 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d12312, d152855, d156646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d12312, d152855, d156646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro30090 (p : Pattern) (ha : d12318 p = 1) (hb : d152855 p = 1) : d156652 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12313 q = 1) (hb : d152855 q = 1) : d156647 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12313, d156647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30089 q ha hb
    | true =>
      simp only [d12313, d156647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30067 q ha hb
  have h2 (q : Pattern) (ha : d12314 q = 1) (hb : d152855 q = 1) : d156648 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12314, d156648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12314, d156648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12315 q = 1) (hb : d152855 q = 1) : d156649 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12315, d156649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12315, d156649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d4819 q = 1) (hb : d152855 q = 1) : d156543 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d4819, d156543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30067 q ha hb
    | true =>
      simp only [d4819, d156543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30049 q ha hb
  have h5 (q : Pattern) (ha : d4820 q = 1) (hb : d152855 q = 1) : d156544 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d4820, d156544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4820, d156544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4821 q = 1) (hb : d152855 q = 1) : d156545 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d4821, d156545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4821, d156545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12316 q = 1) (hb : d152855 q = 1) : d156650 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12316, d156650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12316, d156650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d31 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30049 q ha hb
    | true =>
      simp only [d31, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d32 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d32, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d33 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d12225 q = 1) (hb : d152855 q = 1) : d156546 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12225, d156546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12225, d156546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d12317 q = 1) (hb : d152855 q = 1) : d156651 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12317, d156651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12317, d156651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d12318 q = 1) (hb : d152855 q = 1) : d156652 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12318, d156652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d12318, d156652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro30091 (p : Pattern) (ha : d12324 p = 1) (hb : d152855 p = 1) : d156658 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12319 q = 1) (hb : d152855 q = 1) : d156653 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12319, d156653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30090 q ha hb
    | true =>
      simp only [d12319, d156653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12320 q = 1) (hb : d152855 q = 1) : d156654 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12320, d156654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12320, d156654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12228 q = 1) (hb : d152855 q = 1) : d156549 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12228, d156549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30068 q ha hb
    | true =>
      simp only [d12228, d156549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12229 q = 1) (hb : d152855 q = 1) : d156550 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12229, d156550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12229, d156550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12321 q = 1) (hb : d152855 q = 1) : d156655 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12321, d156655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12321, d156655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12322 q = 1) (hb : d152855 q = 1) : d156656 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12322, d156656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12322, d156656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12323 q = 1) (hb : d152855 q = 1) : d156657 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12323, d156657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12323, d156657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12324 q = 1) (hb : d152855 q = 1) : d156658 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12324, d156658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12324, d156658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro30092 (p : Pattern) (ha : d12344 p = 1) (hb : d152855 p = 1) : d156554 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12228 q = 1) (hb : d152855 q = 1) : d156549 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12228, d156549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30068 q ha hb
    | true =>
      simp only [d12228, d156549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12229 q = 1) (hb : d152855 q = 1) : d156550 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12229, d156550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12229, d156550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12341 q = 1) (hb : d152855 q = 1) : d156551 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12341, d156551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12341, d156551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12342 q = 1) (hb : d152855 q = 1) : d156552 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12342, d156552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12342, d156552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12343 q = 1) (hb : d152855 q = 1) : d156553 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12343, d156553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12343, d156553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12344 q = 1) (hb : d152855 q = 1) : d156554 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12344, d156554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12344, d156554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro30093 (p : Pattern) (ha : d115280 p = 1) (hb : d152855 p = 1) : d156664 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12302 q = 1) (hb : d152855 q = 1) : d156630 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12302, d156630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30086 q ha hb
    | true =>
      simp only [d12302, d156630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30064 q ha hb
  have h2 (q : Pattern) (ha : d12303 q = 1) (hb : d152855 q = 1) : d156631 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12303, d156631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12303, d156631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12304 q = 1) (hb : d152855 q = 1) : d156632 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12304, d156632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12304, d156632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12305 q = 1) (hb : d152855 q = 1) : d156633 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12305, d156633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12305, d156633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12309 q = 1) (hb : d152855 q = 1) : d156637 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12309, d156637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30087 q ha hb
    | true =>
      simp only [d12309, d156637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30065 q ha hb
  have h6 (q : Pattern) (ha : d12310 q = 1) (hb : d152855 q = 1) : d156638 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12310, d156638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12310, d156638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12311 q = 1) (hb : d152855 q = 1) : d156639 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12311, d156639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12311, d156639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12325 q = 1) (hb : d152855 q = 1) : d156659 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12325, d156659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30091 q ha hb
    | true =>
      simp only [d12325, d156659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30069 q ha hb
  have h9 (q : Pattern) (ha : d115276 q = 1) (hb : d152855 q = 1) : d156660 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115276, d156660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d115276, d156660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d12345 q = 1) (hb : d152855 q = 1) : d156555 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12345, d156555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30092 q ha hb
    | true =>
      simp only [d12345, d156555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d12346 q = 1) (hb : d152855 q = 1) : d156556 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12346, d156556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d12346, d156556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d115277 q = 1) (hb : d152855 q = 1) : d156661 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115277, d156661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d115277, d156661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d115278 q = 1) (hb : d152855 q = 1) : d156662 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115278, d156662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d115278, d156662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d115279 q = 1) (hb : d152855 q = 1) : d156663 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115279, d156663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115279, d156663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d115280 q = 1) (hb : d152855 q = 1) : d156664 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115280, d156664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115280, d156664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro30094 (p : Pattern) (ha : d12351 p = 1) (hb : d152855 p = 1) : d156665 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12228 q = 1) (hb : d152855 q = 1) : d156549 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12228, d156549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30068 q ha hb
    | true =>
      simp only [d12228, d156549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12229 q = 1) (hb : d152855 q = 1) : d156550 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12229, d156550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12229, d156550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30050 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12230 q = 1) (hb : d152855 q = 1) : d156551 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12230, d156551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12230, d156551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12231 q = 1) (hb : d152855 q = 1) : d156552 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12231, d156552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12231, d156552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12300 q = 1) (hb : d152855 q = 1) : d156628 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12300, d156628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12300, d156628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12351 q = 1) (hb : d152855 q = 1) : d156665 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12351, d156665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12351, d156665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro30095 (p : Pattern) (ha : d12356 p = 1) (hb : d152855 p = 1) : d156670 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12228 q = 1) (hb : d152855 q = 1) : d156549 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12228, d156549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30068 q ha hb
    | true =>
      simp only [d12228, d156549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12229 q = 1) (hb : d152855 q = 1) : d156550 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12229, d156550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12229, d156550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30050 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12230 q = 1) (hb : d152855 q = 1) : d156551 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12230, d156551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12230, d156551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12306 q = 1) (hb : d152855 q = 1) : d156634 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12306, d156634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12306, d156634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12307 q = 1) (hb : d152855 q = 1) : d156635 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12307, d156635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12307, d156635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12356 q = 1) (hb : d152855 q = 1) : d156670 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12356, d156670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12356, d156670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro30096 (p : Pattern) (ha : d12360 p = 1) (hb : d152855 p = 1) : d156674 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12319 q = 1) (hb : d152855 q = 1) : d156653 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12319, d156653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30090 q ha hb
    | true =>
      simp only [d12319, d156653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12320 q = 1) (hb : d152855 q = 1) : d156654 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12320, d156654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12320, d156654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12228 q = 1) (hb : d152855 q = 1) : d156549 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12228, d156549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30068 q ha hb
    | true =>
      simp only [d12228, d156549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12229 q = 1) (hb : d152855 q = 1) : d156550 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12229, d156550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12229, d156550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12321 q = 1) (hb : d152855 q = 1) : d156655 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12321, d156655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12321, d156655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12322 q = 1) (hb : d152855 q = 1) : d156656 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12322, d156656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12322, d156656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12323 q = 1) (hb : d152855 q = 1) : d156657 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12323, d156657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12323, d156657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12360 q = 1) (hb : d152855 q = 1) : d156674 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12360, d156674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12360, d156674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro30097 (p : Pattern) (ha : d12365 p = 1) (hb : d152855 p = 1) : d156561 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12228 q = 1) (hb : d152855 q = 1) : d156549 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12228, d156549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30068 q ha hb
    | true =>
      simp only [d12228, d156549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12229 q = 1) (hb : d152855 q = 1) : d156550 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12229, d156550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12229, d156550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12341 q = 1) (hb : d152855 q = 1) : d156551 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12341, d156551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12341, d156551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12342 q = 1) (hb : d152855 q = 1) : d156552 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12342, d156552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12342, d156552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12343 q = 1) (hb : d152855 q = 1) : d156553 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12343, d156553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12343, d156553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12365 q = 1) (hb : d152855 q = 1) : d156561 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12365, d156561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12365, d156561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro30098 (p : Pattern) (ha : d115285 p = 1) (hb : d152855 p = 1) : d156680 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12302 q = 1) (hb : d152855 q = 1) : d156630 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12302, d156630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30086 q ha hb
    | true =>
      simp only [d12302, d156630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30064 q ha hb
  have h2 (q : Pattern) (ha : d12303 q = 1) (hb : d152855 q = 1) : d156631 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12303, d156631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12303, d156631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12304 q = 1) (hb : d152855 q = 1) : d156632 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12304, d156632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12304, d156632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12305 q = 1) (hb : d152855 q = 1) : d156633 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12305, d156633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12305, d156633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12309 q = 1) (hb : d152855 q = 1) : d156637 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12309, d156637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30087 q ha hb
    | true =>
      simp only [d12309, d156637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30065 q ha hb
  have h6 (q : Pattern) (ha : d12310 q = 1) (hb : d152855 q = 1) : d156638 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12310, d156638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12310, d156638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12311 q = 1) (hb : d152855 q = 1) : d156639 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12311, d156639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12311, d156639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12325 q = 1) (hb : d152855 q = 1) : d156659 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12325, d156659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30091 q ha hb
    | true =>
      simp only [d12325, d156659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30069 q ha hb
  have h9 (q : Pattern) (ha : d115276 q = 1) (hb : d152855 q = 1) : d156660 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115276, d156660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d115276, d156660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d12345 q = 1) (hb : d152855 q = 1) : d156555 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12345, d156555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30092 q ha hb
    | true =>
      simp only [d12345, d156555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d12346 q = 1) (hb : d152855 q = 1) : d156556 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12346, d156556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d12346, d156556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d115277 q = 1) (hb : d152855 q = 1) : d156661 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115277, d156661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d115277, d156661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d115278 q = 1) (hb : d152855 q = 1) : d156662 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115278, d156662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d115278, d156662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d115279 q = 1) (hb : d152855 q = 1) : d156663 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115279, d156663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115279, d156663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d12352 q = 1) (hb : d152855 q = 1) : d156666 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12352, d156666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30094 q ha hb
    | true =>
      simp only [d12352, d156666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30071 q ha hb
  have h16 (q : Pattern) (ha : d12353 q = 1) (hb : d152855 q = 1) : d156667 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12353, d156667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12353, d156667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d12354 q = 1) (hb : d152855 q = 1) : d156668 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12354, d156668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d12354, d156668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d12355 q = 1) (hb : d152855 q = 1) : d156669 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12355, d156669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12355, d156669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d12357 q = 1) (hb : d152855 q = 1) : d156671 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12357, d156671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30095 q ha hb
    | true =>
      simp only [d12357, d156671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30072 q ha hb
  have h20 (q : Pattern) (ha : d12358 q = 1) (hb : d152855 q = 1) : d156672 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12358, d156672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12358, d156672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d12359 q = 1) (hb : d152855 q = 1) : d156673 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12359, d156673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d12359, d156673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d12361 q = 1) (hb : d152855 q = 1) : d156675 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12361, d156675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30096 q ha hb
    | true =>
      simp only [d12361, d156675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30073 q ha hb
  have h23 (q : Pattern) (ha : d115281 q = 1) (hb : d152855 q = 1) : d156676 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115281, d156676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d115281, d156676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d12366 q = 1) (hb : d152855 q = 1) : d156562 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12366, d156562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30097 q ha hb
    | true =>
      simp only [d12366, d156562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d12367 q = 1) (hb : d152855 q = 1) : d156563 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12367, d156563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d12367, d156563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d115282 q = 1) (hb : d152855 q = 1) : d156677 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115282, d156677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d115282, d156677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d115283 q = 1) (hb : d152855 q = 1) : d156678 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115283, d156678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d115283, d156678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d115284 q = 1) (hb : d152855 q = 1) : d156679 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115284, d156679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d115284, d156679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d115285 q = 1) (hb : d152855 q = 1) : d156680 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115285, d156680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d115285, d156680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro30099 (p : Pattern) (ha : d115292 p = 1) (hb : d152855 p = 1) : d156689 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12361 q = 1) (hb : d152855 q = 1) : d156675 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12361, d156675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30096 q ha hb
    | true =>
      simp only [d12361, d156675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30073 q ha hb
  have h2 (q : Pattern) (ha : d115281 q = 1) (hb : d152855 q = 1) : d156676 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115281, d156676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115281, d156676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d12366 q = 1) (hb : d152855 q = 1) : d156562 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12366, d156562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30097 q ha hb
    | true =>
      simp only [d12366, d156562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12367 q = 1) (hb : d152855 q = 1) : d156563 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12367, d156563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12367, d156563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d115282 q = 1) (hb : d152855 q = 1) : d156677 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115282, d156677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115282, d156677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115290 q = 1) (hb : d152855 q = 1) : d156687 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115290, d156687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115290, d156687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d115291 q = 1) (hb : d152855 q = 1) : d156688 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115291, d156688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115291, d156688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d115292 q = 1) (hb : d152855 q = 1) : d156689 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115292, d156689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115292, d156689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro30100 (p : Pattern) (ha : d12386 p = 1) (hb : d152855 p = 1) : d156700 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d412 q = 1) (hb : d152854 q = 1) : d156695 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d412, d156695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d412, d156695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30088 q ha hb
  have h2 (q : Pattern) (ha : d319 q = 1) (hb : d152854 q = 1) : d156641 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319, d156641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30088 q ha hb
    | true =>
      simp only [d319, d156641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d413 q = 1) (hb : d152854 q = 1) : d156696 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d413, d156696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d413, d156696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d320 q = 1) (hb : d152854 q = 1) : d156642 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d320, d156642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d320, d156642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d414 q = 1) (hb : d152854 q = 1) : d156697 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d414, d156697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d414, d156697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d415 q = 1) (hb : d152854 q = 1) : d156698 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d415, d156698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d415, d156698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d226 q = 1) (hb : d152854 q = 1) : d156578 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d226, d156578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d226, d156578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30066 q ha hb
  have h8 (q : Pattern) (ha : d139 q = 1) (hb : d152854 q = 1) : d156537 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d139, d156537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30066 q ha hb
    | true =>
      simp only [d139, d156537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d227 q = 1) (hb : d152854 q = 1) : d156579 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d227, d156579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d227, d156579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d140 q = 1) (hb : d152854 q = 1) : d156538 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d140, d156538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d140, d156538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d228 q = 1) (hb : d152854 q = 1) : d156580 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d228, d156580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d228, d156580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d229 q = 1) (hb : d152854 q = 1) : d156581 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d229, d156581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d229, d156581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d416 q = 1) (hb : d152854 q = 1) : d156699 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d416, d156699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d416, d156699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d12386 q = 1) (hb : d152855 q = 1) : d156700 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d12386, d152855, d156700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d12386, d152855, d156700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro30101 (p : Pattern) (ha : d12392 p = 1) (hb : d152855 p = 1) : d156706 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12387 q = 1) (hb : d152855 q = 1) : d156701 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12387, d156701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30100 q ha hb
    | true =>
      simp only [d12387, d156701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30076 q ha hb
  have h2 (q : Pattern) (ha : d12388 q = 1) (hb : d152855 q = 1) : d156702 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12388, d156702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12388, d156702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12389 q = 1) (hb : d152855 q = 1) : d156703 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12389, d156703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12389, d156703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d6079 q = 1) (hb : d152855 q = 1) : d156584 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d6079, d156584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30076 q ha hb
    | true =>
      simp only [d6079, d156584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30056 q ha hb
  have h5 (q : Pattern) (ha : d6080 q = 1) (hb : d152855 q = 1) : d156585 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d6080, d156585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6080, d156585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6081 q = 1) (hb : d152855 q = 1) : d156586 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d6081, d156586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6081, d156586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12390 q = 1) (hb : d152855 q = 1) : d156704 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12390, d156704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12390, d156704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d72 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d72, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30056 q ha hb
    | true =>
      simp only [d72, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d73 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d73, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d73, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d74 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d74, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d12259 q = 1) (hb : d152855 q = 1) : d156587 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12259, d156587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12259, d156587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d12391 q = 1) (hb : d152855 q = 1) : d156705 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12391, d156705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12391, d156705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d12392 q = 1) (hb : d152855 q = 1) : d156706 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12392, d156706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d12392, d156706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro30102 (p : Pattern) (ha : d12398 p = 1) (hb : d152855 p = 1) : d156712 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12393 q = 1) (hb : d152855 q = 1) : d156707 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12393, d156707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30101 q ha hb
    | true =>
      simp only [d12393, d156707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12394 q = 1) (hb : d152855 q = 1) : d156708 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12394, d156708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12394, d156708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12262 q = 1) (hb : d152855 q = 1) : d156590 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12262, d156590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30077 q ha hb
    | true =>
      simp only [d12262, d156590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12263 q = 1) (hb : d152855 q = 1) : d156591 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12263, d156591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12263, d156591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12395 q = 1) (hb : d152855 q = 1) : d156709 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12395, d156709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12395, d156709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12396 q = 1) (hb : d152855 q = 1) : d156710 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12396, d156710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12396, d156710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12397 q = 1) (hb : d152855 q = 1) : d156711 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12397, d156711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12397, d156711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12398 q = 1) (hb : d152855 q = 1) : d156712 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12398, d156712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12398, d156712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro30103 (p : Pattern) (ha : d12418 p = 1) (hb : d152855 p = 1) : d156595 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12262 q = 1) (hb : d152855 q = 1) : d156590 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12262, d156590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30077 q ha hb
    | true =>
      simp only [d12262, d156590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12263 q = 1) (hb : d152855 q = 1) : d156591 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12263, d156591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12263, d156591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12415 q = 1) (hb : d152855 q = 1) : d156592 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12415, d156592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12415, d156592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12416 q = 1) (hb : d152855 q = 1) : d156593 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12416, d156593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12416, d156593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12417 q = 1) (hb : d152855 q = 1) : d156594 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12417, d156594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12417, d156594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12418 q = 1) (hb : d152855 q = 1) : d156595 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12418, d156595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12418, d156595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro30104 (p : Pattern) (ha : d115302 p = 1) (hb : d152855 p = 1) : d156718 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12399 q = 1) (hb : d152855 q = 1) : d156713 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12399, d156713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30102 q ha hb
    | true =>
      simp only [d12399, d156713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30078 q ha hb
  have h2 (q : Pattern) (ha : d115298 q = 1) (hb : d152855 q = 1) : d156714 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115298, d156714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115298, d156714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d12419 q = 1) (hb : d152855 q = 1) : d156596 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12419, d156596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30103 q ha hb
    | true =>
      simp only [d12419, d156596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12420 q = 1) (hb : d152855 q = 1) : d156597 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12420, d156597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12420, d156597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d115299 q = 1) (hb : d152855 q = 1) : d156715 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115299, d156715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115299, d156715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115300 q = 1) (hb : d152855 q = 1) : d156716 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115300, d156716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115300, d156716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d115301 q = 1) (hb : d152855 q = 1) : d156717 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115301, d156717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115301, d156717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d115302 q = 1) (hb : d152855 q = 1) : d156718 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115302, d156718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115302, d156718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro30105 (p : Pattern) (ha : d115308 p = 1) (hb : d152855 p = 1) : d156724 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12290 q = 1) (hb : d152855 q = 1) : d156618 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12290, d156618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12290, d156618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30083 q ha hb
  have h2 (q : Pattern) (ha : d12291 q = 1) (hb : d152855 q = 1) : d156619 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d12291, d156619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d12291, d156619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d12297 q = 1) (hb : d152855 q = 1) : d156625 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12297, d156625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30083 q ha hb
    | true =>
      simp only [d12297, d156625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30084 q ha hb
  have h4 (q : Pattern) (ha : d12298 q = 1) (hb : d152855 q = 1) : d156626 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d12298, d156626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12298, d156626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12299 q = 1) (hb : d152855 q = 1) : d156627 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d12299, d156627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12299, d156627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115286 q = 1) (hb : d152855 q = 1) : d156681 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115286, d156681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30093 q ha hb
    | true =>
      simp only [d115286, d156681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30098 q ha hb
  have h7 (q : Pattern) (ha : d12374 q = 1) (hb : d152855 q = 1) : d156683 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12374, d156683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30085 q ha hb
    | true =>
      simp only [d12374, d156683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30062 q ha hb
  have h8 (q : Pattern) (ha : d115287 q = 1) (hb : d152855 q = 1) : d156684 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115287, d156684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d115287, d156684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d115288 q = 1) (hb : d152855 q = 1) : d156685 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115288, d156685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d115288, d156685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d115289 q = 1) (hb : d152855 q = 1) : d156686 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115289, d156686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d115289, d156686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d115293 q = 1) (hb : d152855 q = 1) : d156690 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115293, d156690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115293, d156690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30099 q ha hb
  have h12 (q : Pattern) (ha : d407 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30081 q ha hb
  have h13 (q : Pattern) (ha : d115294 q = 1) (hb : d152855 q = 1) : d156691 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115294, d156691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d115294, d156691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d115295 q = 1) (hb : d152855 q = 1) : d156692 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115295, d156692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d115295, d156692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d115296 q = 1) (hb : d152855 q = 1) : d156693 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115296, d156693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d115296, d156693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d115297 q = 1) (hb : d152855 q = 1) : d156694 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d115297, d156694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d115297, d156694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d115303 q = 1) (hb : d152855 q = 1) : d156719 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115303, d156719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115303, d156719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30104 q ha hb
  have h18 (q : Pattern) (ha : d463 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30082 q ha hb
  have h19 (q : Pattern) (ha : d115304 q = 1) (hb : d152855 q = 1) : d156720 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115304, d156720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d115304, d156720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d115305 q = 1) (hb : d152855 q = 1) : d156721 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115305, d156721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d115305, d156721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d115306 q = 1) (hb : d152855 q = 1) : d156722 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115306, d156722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d115306, d156722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d115307 q = 1) (hb : d152855 q = 1) : d156723 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d115307, d156723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d115307, d156723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d115308 q = 1) (hb : d152855 q = 1) : d156724 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d115308, d156724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d115308, d156724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro30106 (p : Pattern) (ha : d115314 p = 1) (hb : d152855 p = 1) : d156730 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d96, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d96, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30060 q ha hb
  have h2 (q : Pattern) (ha : d97 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d97, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d97, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d98 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d98, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d98, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d99 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d99, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d99, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d115271 q = 1) (hb : d152855 q = 1) : d156608 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d115271, d156608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115271, d156608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30080 q ha hb
  have h6 (q : Pattern) (ha : d115272 q = 1) (hb : d152855 q = 1) : d156609 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d115272, d156609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115272, d156609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d115273 q = 1) (hb : d152855 q = 1) : d156610 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d115273, d156610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115273, d156610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d115274 q = 1) (hb : d152855 q = 1) : d156611 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d115274, d156611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115274, d156611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d115275 q = 1) (hb : d152855 q = 1) : d156612 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d115275, d156612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115275, d156612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d115309 q = 1) (hb : d152855 q = 1) : d156725 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d115309, d156725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115309, d156725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30105 q ha hb
  have h11 (q : Pattern) (ha : d115310 q = 1) (hb : d152855 q = 1) : d156726 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d115310, d156726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115310, d156726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d115311 q = 1) (hb : d152855 q = 1) : d156727 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d115311, d156727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115311, d156727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d115312 q = 1) (hb : d152855 q = 1) : d156728 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d115312, d156728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115312, d156728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d115313 q = 1) (hb : d152855 q = 1) : d156729 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d115313, d156729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115313, d156729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d115314 q = 1) (hb : d152855 q = 1) : d156730 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d115314, d156730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d115314, d156730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro30107 (p : Pattern) (ha : d12438 p = 1) (hb : d152855 p = 1) : d156652 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12313 q = 1) (hb : d152855 q = 1) : d156647 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12313, d156647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30089 q ha hb
    | true =>
      simp only [d12313, d156647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30067 q ha hb
  have h2 (q : Pattern) (ha : d12314 q = 1) (hb : d152855 q = 1) : d156648 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12314, d156648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12314, d156648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12315 q = 1) (hb : d152855 q = 1) : d156649 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12315, d156649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12315, d156649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d4819 q = 1) (hb : d152855 q = 1) : d156543 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d4819, d156543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30067 q ha hb
    | true =>
      simp only [d4819, d156543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30049 q ha hb
  have h5 (q : Pattern) (ha : d4820 q = 1) (hb : d152855 q = 1) : d156544 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d4820, d156544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4820, d156544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4821 q = 1) (hb : d152855 q = 1) : d156545 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d4821, d156545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4821, d156545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12316 q = 1) (hb : d152855 q = 1) : d156650 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12316, d156650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12316, d156650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d4822 q = 1) (hb : d152855 q = 1) : d156546 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d4822, d156546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d4822, d156546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d12437 q = 1) (hb : d152855 q = 1) : d156651 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12437, d156651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12437, d156651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d12438 q = 1) (hb : d152855 q = 1) : d156652 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12438, d156652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d12438, d156652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro30108 (p : Pattern) (ha : d12442 p = 1) (hb : d152855 p = 1) : d156548 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4819 q = 1) (hb : d152855 q = 1) : d156543 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d4819, d156543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30067 q ha hb
    | true =>
      simp only [d4819, d156543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30049 q ha hb
  have h2 (q : Pattern) (ha : d4820 q = 1) (hb : d152855 q = 1) : d156544 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d4820, d156544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4820, d156544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d4821 q = 1) (hb : d152855 q = 1) : d156545 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d4821, d156545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4821, d156545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d4822 q = 1) (hb : d152855 q = 1) : d156546 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d4822, d156546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4822, d156546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12441 q = 1) (hb : d152855 q = 1) : d156547 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12441, d156547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12441, d156547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12442 q = 1) (hb : d152855 q = 1) : d156548 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12442, d156548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12442, d156548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro30109 (p : Pattern) (ha : d12448 p = 1) (hb : d152855 p = 1) : d156658 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12439 q = 1) (hb : d152855 q = 1) : d156653 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12439, d156653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30107 q ha hb
    | true =>
      simp only [d12439, d156653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12440 q = 1) (hb : d152855 q = 1) : d156654 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12440, d156654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12440, d156654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12443 q = 1) (hb : d152855 q = 1) : d156549 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12443, d156549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30108 q ha hb
    | true =>
      simp only [d12443, d156549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12444 q = 1) (hb : d152855 q = 1) : d156550 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12444, d156550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12444, d156550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12445 q = 1) (hb : d152855 q = 1) : d156655 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12445, d156655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12445, d156655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12446 q = 1) (hb : d152855 q = 1) : d156656 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12446, d156656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12446, d156656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12447 q = 1) (hb : d152855 q = 1) : d156657 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12447, d156657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12447, d156657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12448 q = 1) (hb : d152855 q = 1) : d156658 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12448, d156658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12448, d156658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro30110 (p : Pattern) (ha : d12452 p = 1) (hb : d152855 p = 1) : d156554 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12443 q = 1) (hb : d152855 q = 1) : d156549 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12443, d156549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30108 q ha hb
    | true =>
      simp only [d12443, d156549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12444 q = 1) (hb : d152855 q = 1) : d156550 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12444, d156550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12444, d156550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12449 q = 1) (hb : d152855 q = 1) : d156551 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12449, d156551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12449, d156551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12450 q = 1) (hb : d152855 q = 1) : d156552 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12450, d156552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12450, d156552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12451 q = 1) (hb : d152855 q = 1) : d156553 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12451, d156553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12451, d156553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12452 q = 1) (hb : d152855 q = 1) : d156554 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12452, d156554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12452, d156554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro30111 (p : Pattern) (ha : d12458 p = 1) (hb : d152855 p = 1) : d156735 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12453 q = 1) (hb : d152855 q = 1) : d156659 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12453, d156659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30109 q ha hb
    | true =>
      simp only [d12453, d156659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30110 q ha hb
  have h2 (q : Pattern) (ha : d12454 q = 1) (hb : d152855 q = 1) : d156731 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12454, d156731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12454, d156731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12455 q = 1) (hb : d152855 q = 1) : d156732 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12455, d156732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12455, d156732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12456 q = 1) (hb : d152855 q = 1) : d156733 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12456, d156733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12456, d156733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12457 q = 1) (hb : d152855 q = 1) : d156734 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12457, d156734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12457, d156734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12458 q = 1) (hb : d152855 q = 1) : d156735 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d12458, d156735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12458, d156735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro30112 (p : Pattern) (ha : d12461 p = 1) (hb : d152855 p = 1) : d156674 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12439 q = 1) (hb : d152855 q = 1) : d156653 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12439, d156653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30107 q ha hb
    | true =>
      simp only [d12439, d156653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12440 q = 1) (hb : d152855 q = 1) : d156654 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12440, d156654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12440, d156654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12443 q = 1) (hb : d152855 q = 1) : d156549 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12443, d156549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30108 q ha hb
    | true =>
      simp only [d12443, d156549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12444 q = 1) (hb : d152855 q = 1) : d156550 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12444, d156550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12444, d156550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12445 q = 1) (hb : d152855 q = 1) : d156655 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12445, d156655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12445, d156655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12446 q = 1) (hb : d152855 q = 1) : d156656 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12446, d156656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12446, d156656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12447 q = 1) (hb : d152855 q = 1) : d156657 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12447, d156657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12447, d156657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12461 q = 1) (hb : d152855 q = 1) : d156674 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12461, d156674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12461, d156674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro30113 (p : Pattern) (ha : d12462 p = 1) (hb : d152855 p = 1) : d156561 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12443 q = 1) (hb : d152855 q = 1) : d156549 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12443, d156549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30108 q ha hb
    | true =>
      simp only [d12443, d156549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12444 q = 1) (hb : d152855 q = 1) : d156550 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12444, d156550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12444, d156550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12449 q = 1) (hb : d152855 q = 1) : d156551 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12449, d156551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12449, d156551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12450 q = 1) (hb : d152855 q = 1) : d156552 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12450, d156552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12450, d156552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12451 q = 1) (hb : d152855 q = 1) : d156553 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12451, d156553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12451, d156553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12462 q = 1) (hb : d152855 q = 1) : d156561 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12462, d156561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12462, d156561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro30114 (p : Pattern) (ha : d12468 p = 1) (hb : d152855 p = 1) : d156742 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12453 q = 1) (hb : d152855 q = 1) : d156659 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12453, d156659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30109 q ha hb
    | true =>
      simp only [d12453, d156659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30110 q ha hb
  have h2 (q : Pattern) (ha : d12454 q = 1) (hb : d152855 q = 1) : d156731 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12454, d156731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12454, d156731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12455 q = 1) (hb : d152855 q = 1) : d156732 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12455, d156732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12455, d156732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12456 q = 1) (hb : d152855 q = 1) : d156733 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12456, d156733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12456, d156733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12457 q = 1) (hb : d152855 q = 1) : d156734 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12457, d156734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12457, d156734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12463 q = 1) (hb : d152855 q = 1) : d156675 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12463, d156675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30112 q ha hb
    | true =>
      simp only [d12463, d156675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30113 q ha hb
  have h7 (q : Pattern) (ha : d12464 q = 1) (hb : d152855 q = 1) : d156738 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12464, d156738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12464, d156738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12465 q = 1) (hb : d152855 q = 1) : d156739 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12465, d156739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12465, d156739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d12466 q = 1) (hb : d152855 q = 1) : d156740 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12466, d156740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12466, d156740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d12467 q = 1) (hb : d152855 q = 1) : d156741 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12467, d156741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12467, d156741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d12468 q = 1) (hb : d152855 q = 1) : d156742 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d12468, d156742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12468, d156742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro30115 (p : Pattern) (ha : d12574 p = 1) (hb : d152855 p = 1) : d156809 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12453 q = 1) (hb : d152855 q = 1) : d156659 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12453, d156659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30109 q ha hb
    | true =>
      simp only [d12453, d156659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30110 q ha hb
  have h2 (q : Pattern) (ha : d12454 q = 1) (hb : d152855 q = 1) : d156731 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12454, d156731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12454, d156731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12455 q = 1) (hb : d152855 q = 1) : d156732 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12455, d156732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12455, d156732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12456 q = 1) (hb : d152855 q = 1) : d156733 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12456, d156733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12456, d156733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12457 q = 1) (hb : d152855 q = 1) : d156734 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12457, d156734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12457, d156734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12569 q = 1) (hb : d152855 q = 1) : d156555 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12569, d156555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30110 q ha hb
    | true =>
      simp only [d12569, d156555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12570 q = 1) (hb : d152855 q = 1) : d156613 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12570, d156613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12570, d156613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12571 q = 1) (hb : d152855 q = 1) : d156614 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12571, d156614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12571, d156614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d12572 q = 1) (hb : d152855 q = 1) : d156615 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12572, d156615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12572, d156615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d12573 q = 1) (hb : d152855 q = 1) : d156616 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12573, d156616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12573, d156616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d12574 q = 1) (hb : d152855 q = 1) : d156809 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d12574, d156809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12574, d156809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro30116 (p : Pattern) (ha : d12580 p = 1) (hb : d152855 p = 1) : d156624 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12569 q = 1) (hb : d152855 q = 1) : d156555 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12569, d156555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30110 q ha hb
    | true =>
      simp only [d12569, d156555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12570 q = 1) (hb : d152855 q = 1) : d156613 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12570, d156613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12570, d156613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12571 q = 1) (hb : d152855 q = 1) : d156614 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12571, d156614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12571, d156614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12572 q = 1) (hb : d152855 q = 1) : d156615 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12572, d156615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12572, d156615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12573 q = 1) (hb : d152855 q = 1) : d156616 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12573, d156616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12573, d156616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12575 q = 1) (hb : d152855 q = 1) : d156562 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12575, d156562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30113 q ha hb
    | true =>
      simp only [d12575, d156562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12576 q = 1) (hb : d152855 q = 1) : d156620 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12576, d156620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12576, d156620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12577 q = 1) (hb : d152855 q = 1) : d156621 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12577, d156621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12577, d156621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d12578 q = 1) (hb : d152855 q = 1) : d156622 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12578, d156622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12578, d156622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d12579 q = 1) (hb : d152855 q = 1) : d156623 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12579, d156623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12579, d156623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d12580 q = 1) (hb : d152855 q = 1) : d156624 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d12580, d156624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12580, d156624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro30117 (p : Pattern) (ha : d12589 p = 1) (hb : d152855 p = 1) : d156818 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12575 q = 1) (hb : d152855 q = 1) : d156562 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12575, d156562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30113 q ha hb
    | true =>
      simp only [d12575, d156562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12576 q = 1) (hb : d152855 q = 1) : d156620 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12576, d156620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12576, d156620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12577 q = 1) (hb : d152855 q = 1) : d156621 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12577, d156621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12577, d156621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12578 q = 1) (hb : d152855 q = 1) : d156622 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12578, d156622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12578, d156622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12579 q = 1) (hb : d152855 q = 1) : d156623 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12579, d156623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12579, d156623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12589 q = 1) (hb : d152855 q = 1) : d156818 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d12589, d156818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12589, d156818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro30118 (p : Pattern) (ha : d12622 p = 1) (hb : d152855 p = 1) : d156589 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6079 q = 1) (hb : d152855 q = 1) : d156584 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d6079, d156584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30076 q ha hb
    | true =>
      simp only [d6079, d156584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30056 q ha hb
  have h2 (q : Pattern) (ha : d6080 q = 1) (hb : d152855 q = 1) : d156585 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d6080, d156585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6080, d156585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6081 q = 1) (hb : d152855 q = 1) : d156586 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d6081, d156586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6081, d156586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d6082 q = 1) (hb : d152855 q = 1) : d156587 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d6082, d156587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6082, d156587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12621 q = 1) (hb : d152855 q = 1) : d156588 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12621, d156588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12621, d156588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12622 q = 1) (hb : d152855 q = 1) : d156589 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12622, d156589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12622, d156589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro30119 (p : Pattern) (ha : d12668 p = 1) (hb : d152855 p = 1) : d156595 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12623 q = 1) (hb : d152855 q = 1) : d156590 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12623, d156590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30118 q ha hb
    | true =>
      simp only [d12623, d156590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12624 q = 1) (hb : d152855 q = 1) : d156591 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12624, d156591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12624, d156591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12665 q = 1) (hb : d152855 q = 1) : d156592 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12665, d156592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12665, d156592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12666 q = 1) (hb : d152855 q = 1) : d156593 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12666, d156593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12666, d156593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12667 q = 1) (hb : d152855 q = 1) : d156594 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12667, d156594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12667, d156594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12668 q = 1) (hb : d152855 q = 1) : d156595 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12668, d156595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12668, d156595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro30120 (p : Pattern) (ha : d12674 p = 1) (hb : d152855 p = 1) : d156859 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12669 q = 1) (hb : d152855 q = 1) : d156596 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12669, d156596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30119 q ha hb
    | true =>
      simp only [d12669, d156596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12670 q = 1) (hb : d152855 q = 1) : d156855 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12670, d156855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12670, d156855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12671 q = 1) (hb : d152855 q = 1) : d156856 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12671, d156856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12671, d156856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12672 q = 1) (hb : d152855 q = 1) : d156857 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12672, d156857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12672, d156857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12673 q = 1) (hb : d152855 q = 1) : d156858 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12673, d156858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12673, d156858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12674 q = 1) (hb : d152855 q = 1) : d156859 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d12674, d156859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12674, d156859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro30121 (p : Pattern) (ha : d12473 p = 1) (hb : d152855 p = 1) : d156747 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12439 q = 1) (hb : d152855 q = 1) : d156653 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12439, d156653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30107 q ha hb
    | true =>
      simp only [d12439, d156653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12440 q = 1) (hb : d152855 q = 1) : d156654 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12440, d156654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12440, d156654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12443 q = 1) (hb : d152855 q = 1) : d156549 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12443, d156549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30108 q ha hb
    | true =>
      simp only [d12443, d156549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12444 q = 1) (hb : d152855 q = 1) : d156550 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12444, d156550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12444, d156550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12445 q = 1) (hb : d152855 q = 1) : d156655 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12445, d156655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12445, d156655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12446 q = 1) (hb : d152855 q = 1) : d156656 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12446, d156656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12446, d156656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12472 q = 1) (hb : d152855 q = 1) : d156746 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12472, d156746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12472, d156746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12473 q = 1) (hb : d152855 q = 1) : d156747 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12473, d156747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12473, d156747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro30122 (p : Pattern) (ha : d12475 p = 1) (hb : d152855 p = 1) : d156629 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12443 q = 1) (hb : d152855 q = 1) : d156549 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12443, d156549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30108 q ha hb
    | true =>
      simp only [d12443, d156549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12444 q = 1) (hb : d152855 q = 1) : d156550 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12444, d156550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12444, d156550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12449 q = 1) (hb : d152855 q = 1) : d156551 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12449, d156551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12449, d156551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12450 q = 1) (hb : d152855 q = 1) : d156552 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12450, d156552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12450, d156552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12474 q = 1) (hb : d152855 q = 1) : d156628 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12474, d156628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12474, d156628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12475 q = 1) (hb : d152855 q = 1) : d156629 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12475, d156629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12475, d156629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro30123 (p : Pattern) (ha : d12482 p = 1) (hb : d152855 p = 1) : d156754 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12439 q = 1) (hb : d152855 q = 1) : d156653 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12439, d156653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30107 q ha hb
    | true =>
      simp only [d12439, d156653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12440 q = 1) (hb : d152855 q = 1) : d156654 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12440, d156654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12440, d156654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12443 q = 1) (hb : d152855 q = 1) : d156549 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12443, d156549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30108 q ha hb
    | true =>
      simp only [d12443, d156549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12444 q = 1) (hb : d152855 q = 1) : d156550 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12444, d156550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12444, d156550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12445 q = 1) (hb : d152855 q = 1) : d156655 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12445, d156655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12445, d156655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12480 q = 1) (hb : d152855 q = 1) : d156752 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12480, d156752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12480, d156752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12481 q = 1) (hb : d152855 q = 1) : d156753 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12481, d156753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12481, d156753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12482 q = 1) (hb : d152855 q = 1) : d156754 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12482, d156754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12482, d156754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro30124 (p : Pattern) (ha : d12485 p = 1) (hb : d152855 p = 1) : d156636 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12443 q = 1) (hb : d152855 q = 1) : d156549 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12443, d156549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30108 q ha hb
    | true =>
      simp only [d12443, d156549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12444 q = 1) (hb : d152855 q = 1) : d156550 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12444, d156550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12444, d156550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12449 q = 1) (hb : d152855 q = 1) : d156551 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12449, d156551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12449, d156551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12483 q = 1) (hb : d152855 q = 1) : d156634 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12483, d156634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12483, d156634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12484 q = 1) (hb : d152855 q = 1) : d156635 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12484, d156635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12484, d156635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12485 q = 1) (hb : d152855 q = 1) : d156636 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12485, d156636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12485, d156636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro30125 (p : Pattern) (ha : d542 p = 1) (hb : d152854 p = 1) : d156758 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d541 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d314 q = 1) : d314 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d134 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d315 q = 1) (hb : d152852 q = 1) : d25210 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d315, d152852, d25210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d315, d152852, d25210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d1 q = 1) (hb : d134 q = 1) : d134 q = 1 := by
    exact hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d20 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d135 q = 1) (hb : d152852 q = 1) : d9796 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d135, d152852, d9796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d135, d152852, d9796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d316 q = 1) (hb : d152852 q = 1) : d25211 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d316, d25211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d316, d25211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d152852 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d317 q = 1) (hb : d152852 q = 1) : d25212 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d317, d25212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d317, d25212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d542 q = 1) (hb : d152854 q = 1) : d156758 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d542, d152854, d156758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d542, d152854, d156758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro30126 (p : Pattern) (ha : d12489 p = 1) (hb : d152855 p = 1) : d156764 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d543 q = 1) (hb : d152854 q = 1) : d156759 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d543, d156759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30125 q ha hb
    | true =>
      simp only [d543, d156759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d544 q = 1) (hb : d152854 q = 1) : d156760 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d544, d156760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d544, d156760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d545 q = 1) (hb : d152854 q = 1) : d156761 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d545, d156761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d545, d156761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d546 q = 1) (hb : d152854 q = 1) : d156762 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d546, d156762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d546, d156762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d319 q = 1) (hb : d152854 q = 1) : d156641 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319, d156641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30088 q ha hb
    | true =>
      simp only [d319, d156641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d320 q = 1) (hb : d152854 q = 1) : d156642 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d320, d156642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d320, d156642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d321 q = 1) (hb : d152854 q = 1) : d156643 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d321, d156643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d321, d156643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d322 q = 1) (hb : d152854 q = 1) : d156644 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d322, d156644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d322, d156644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d547 q = 1) (hb : d152854 q = 1) : d156763 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d547, d156763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d547, d156763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d12489 q = 1) (hb : d152855 q = 1) : d156764 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d12489, d152855, d156764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d12489, d152855, d156764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro30127 (p : Pattern) (ha : d9381 p = 1) (hb : d152854 p = 1) : d156536 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d5449 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23 q = 1) (hb : d152852 q = 1) : d23 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d9381 q = 1) (hb : d152854 q = 1) : d156536 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d9381, d152854, d156536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d9381, d152854, d156536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro30128 (p : Pattern) (ha : d12496 p = 1) (hb : d152855 p = 1) : d156542 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9382 q = 1) (hb : d152854 q = 1) : d156537 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9382, d156537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30127 q ha hb
    | true =>
      simp only [d9382, d156537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9384 q = 1) (hb : d152854 q = 1) : d156538 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9384, d156538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d9384, d156538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d12493 q = 1) (hb : d152854 q = 1) : d156539 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d12493, d156539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12493, d156539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d12494 q = 1) (hb : d152854 q = 1) : d156540 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d12494, d156540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12494, d156540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30048 q ha hb
    | true =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d26 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d27 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d27, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d28 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d28, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d28, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d12495 q = 1) (hb : d152854 q = 1) : d156541 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d12495, d156541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12495, d156541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d12496 q = 1) (hb : d152855 q = 1) : d156542 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d12496, d152855, d156542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d12496, d152855, d156542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro30129 (p : Pattern) (ha : d12502 p = 1) (hb : d152855 p = 1) : d156770 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12490 q = 1) (hb : d152855 q = 1) : d156765 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12490, d156765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30126 q ha hb
    | true =>
      simp only [d12490, d156765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30089 q ha hb
  have h2 (q : Pattern) (ha : d12491 q = 1) (hb : d152855 q = 1) : d156766 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12491, d156766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12491, d156766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12492 q = 1) (hb : d152855 q = 1) : d156767 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12492, d156767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12492, d156767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d12497 q = 1) (hb : d152855 q = 1) : d156647 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12497, d156647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30089 q ha hb
    | true =>
      simp only [d12497, d156647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30128 q ha hb
  have h5 (q : Pattern) (ha : d12498 q = 1) (hb : d152855 q = 1) : d156648 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12498, d156648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12498, d156648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12499 q = 1) (hb : d152855 q = 1) : d156649 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12499, d156649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12499, d156649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12500 q = 1) (hb : d152855 q = 1) : d156768 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12500, d156768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12500, d156768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12313 q = 1) (hb : d152855 q = 1) : d156647 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12313, d156647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30089 q ha hb
    | true =>
      simp only [d12313, d156647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30067 q ha hb
  have h9 (q : Pattern) (ha : d12314 q = 1) (hb : d152855 q = 1) : d156648 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12314, d156648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12314, d156648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d12315 q = 1) (hb : d152855 q = 1) : d156649 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12315, d156649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12315, d156649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d4819 q = 1) (hb : d152855 q = 1) : d156543 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d4819, d156543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30067 q ha hb
    | true =>
      simp only [d4819, d156543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30049 q ha hb
  have h12 (q : Pattern) (ha : d4820 q = 1) (hb : d152855 q = 1) : d156544 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d4820, d156544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4820, d156544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d4821 q = 1) (hb : d152855 q = 1) : d156545 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d4821, d156545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4821, d156545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d12316 q = 1) (hb : d152855 q = 1) : d156650 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12316, d156650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d12316, d156650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d12501 q = 1) (hb : d152855 q = 1) : d156769 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12501, d156769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12501, d156769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d12502 q = 1) (hb : d152855 q = 1) : d156770 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12502, d156770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d12502, d156770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro30130 (p : Pattern) (ha : d12508 p = 1) (hb : d152855 p = 1) : d156776 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12503 q = 1) (hb : d152855 q = 1) : d156771 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12503, d156771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30129 q ha hb
    | true =>
      simp only [d12503, d156771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12504 q = 1) (hb : d152855 q = 1) : d156772 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12504, d156772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12504, d156772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12439 q = 1) (hb : d152855 q = 1) : d156653 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12439, d156653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30107 q ha hb
    | true =>
      simp only [d12439, d156653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12440 q = 1) (hb : d152855 q = 1) : d156654 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12440, d156654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12440, d156654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12505 q = 1) (hb : d152855 q = 1) : d156773 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12505, d156773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12505, d156773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12506 q = 1) (hb : d152855 q = 1) : d156774 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12506, d156774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12506, d156774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12507 q = 1) (hb : d152855 q = 1) : d156775 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12507, d156775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12507, d156775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12508 q = 1) (hb : d152855 q = 1) : d156776 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12508, d156776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12508, d156776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro30131 (p : Pattern) (ha : d12537 p = 1) (hb : d152855 p = 1) : d156782 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12439 q = 1) (hb : d152855 q = 1) : d156653 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12439, d156653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30107 q ha hb
    | true =>
      simp only [d12439, d156653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12440 q = 1) (hb : d152855 q = 1) : d156654 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12440, d156654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12440, d156654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12534 q = 1) (hb : d152855 q = 1) : d156779 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12534, d156779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12534, d156779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12535 q = 1) (hb : d152855 q = 1) : d156780 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12535, d156780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12535, d156780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12536 q = 1) (hb : d152855 q = 1) : d156781 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12536, d156781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12536, d156781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12537 q = 1) (hb : d152855 q = 1) : d156782 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12537, d156782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12537, d156782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro30132 (p : Pattern) (ha : d115319 p = 1) (hb : d152855 p = 1) : d156788 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12476 q = 1) (hb : d152855 q = 1) : d156748 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12476, d156748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30121 q ha hb
    | true =>
      simp only [d12476, d156748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30122 q ha hb
  have h2 (q : Pattern) (ha : d12477 q = 1) (hb : d152855 q = 1) : d156749 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12477, d156749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12477, d156749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12478 q = 1) (hb : d152855 q = 1) : d156750 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12478, d156750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12478, d156750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12479 q = 1) (hb : d152855 q = 1) : d156751 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12479, d156751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12479, d156751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12486 q = 1) (hb : d152855 q = 1) : d156755 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12486, d156755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30123 q ha hb
    | true =>
      simp only [d12486, d156755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30124 q ha hb
  have h6 (q : Pattern) (ha : d12487 q = 1) (hb : d152855 q = 1) : d156756 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12487, d156756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12487, d156756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12488 q = 1) (hb : d152855 q = 1) : d156757 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12488, d156757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12488, d156757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12509 q = 1) (hb : d152855 q = 1) : d156777 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12509, d156777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30130 q ha hb
    | true =>
      simp only [d12509, d156777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30109 q ha hb
  have h9 (q : Pattern) (ha : d115315 q = 1) (hb : d152855 q = 1) : d156778 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115315, d156778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d115315, d156778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d12538 q = 1) (hb : d152855 q = 1) : d156783 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12538, d156783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30131 q ha hb
    | true =>
      simp only [d12538, d156783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d12539 q = 1) (hb : d152855 q = 1) : d156784 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12539, d156784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d12539, d156784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d115316 q = 1) (hb : d152855 q = 1) : d156785 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115316, d156785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d115316, d156785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d115317 q = 1) (hb : d152855 q = 1) : d156786 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115317, d156786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d115317, d156786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d115318 q = 1) (hb : d152855 q = 1) : d156787 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115318, d156787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115318, d156787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d115319 q = 1) (hb : d152855 q = 1) : d156788 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115319, d156788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115319, d156788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro30133 (p : Pattern) (ha : d12544 p = 1) (hb : d152855 p = 1) : d156789 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12439 q = 1) (hb : d152855 q = 1) : d156653 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12439, d156653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30107 q ha hb
    | true =>
      simp only [d12439, d156653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12440 q = 1) (hb : d152855 q = 1) : d156654 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12440, d156654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12440, d156654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12443 q = 1) (hb : d152855 q = 1) : d156549 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12443, d156549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30108 q ha hb
    | true =>
      simp only [d12443, d156549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12444 q = 1) (hb : d152855 q = 1) : d156550 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12444, d156550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12444, d156550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12445 q = 1) (hb : d152855 q = 1) : d156655 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12445, d156655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12445, d156655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12446 q = 1) (hb : d152855 q = 1) : d156656 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12446, d156656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12446, d156656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12472 q = 1) (hb : d152855 q = 1) : d156746 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12472, d156746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12472, d156746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12544 q = 1) (hb : d152855 q = 1) : d156789 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12544, d156789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12544, d156789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro30134 (p : Pattern) (ha : d12545 p = 1) (hb : d152855 p = 1) : d156665 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12443 q = 1) (hb : d152855 q = 1) : d156549 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12443, d156549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30108 q ha hb
    | true =>
      simp only [d12443, d156549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12444 q = 1) (hb : d152855 q = 1) : d156550 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12444, d156550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12444, d156550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12449 q = 1) (hb : d152855 q = 1) : d156551 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12449, d156551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12449, d156551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12450 q = 1) (hb : d152855 q = 1) : d156552 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12450, d156552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12450, d156552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12474 q = 1) (hb : d152855 q = 1) : d156628 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12474, d156628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12474, d156628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12545 q = 1) (hb : d152855 q = 1) : d156665 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12545, d156665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12545, d156665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro30135 (p : Pattern) (ha : d12550 p = 1) (hb : d152855 p = 1) : d156794 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12439 q = 1) (hb : d152855 q = 1) : d156653 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12439, d156653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30107 q ha hb
    | true =>
      simp only [d12439, d156653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12440 q = 1) (hb : d152855 q = 1) : d156654 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12440, d156654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12440, d156654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12443 q = 1) (hb : d152855 q = 1) : d156549 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12443, d156549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30108 q ha hb
    | true =>
      simp only [d12443, d156549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12444 q = 1) (hb : d152855 q = 1) : d156550 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12444, d156550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12444, d156550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12445 q = 1) (hb : d152855 q = 1) : d156655 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12445, d156655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12445, d156655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12480 q = 1) (hb : d152855 q = 1) : d156752 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12480, d156752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12480, d156752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12481 q = 1) (hb : d152855 q = 1) : d156753 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12481, d156753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12481, d156753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12550 q = 1) (hb : d152855 q = 1) : d156794 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12550, d156794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12550, d156794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro30136 (p : Pattern) (ha : d12551 p = 1) (hb : d152855 p = 1) : d156670 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12443 q = 1) (hb : d152855 q = 1) : d156549 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12443, d156549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30108 q ha hb
    | true =>
      simp only [d12443, d156549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12444 q = 1) (hb : d152855 q = 1) : d156550 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12444, d156550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12444, d156550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12449 q = 1) (hb : d152855 q = 1) : d156551 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12449, d156551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12449, d156551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12483 q = 1) (hb : d152855 q = 1) : d156634 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12483, d156634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12483, d156634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12484 q = 1) (hb : d152855 q = 1) : d156635 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12484, d156635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12484, d156635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12551 q = 1) (hb : d152855 q = 1) : d156670 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12551, d156670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12551, d156670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro30137 (p : Pattern) (ha : d12555 p = 1) (hb : d152855 p = 1) : d156798 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12503 q = 1) (hb : d152855 q = 1) : d156771 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12503, d156771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30129 q ha hb
    | true =>
      simp only [d12503, d156771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12504 q = 1) (hb : d152855 q = 1) : d156772 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12504, d156772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12504, d156772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12439 q = 1) (hb : d152855 q = 1) : d156653 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12439, d156653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30107 q ha hb
    | true =>
      simp only [d12439, d156653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12440 q = 1) (hb : d152855 q = 1) : d156654 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12440, d156654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12440, d156654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12505 q = 1) (hb : d152855 q = 1) : d156773 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12505, d156773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12505, d156773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12506 q = 1) (hb : d152855 q = 1) : d156774 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12506, d156774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12506, d156774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12507 q = 1) (hb : d152855 q = 1) : d156775 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12507, d156775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12507, d156775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12555 q = 1) (hb : d152855 q = 1) : d156798 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12555, d156798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12555, d156798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro30138 (p : Pattern) (ha : d12561 p = 1) (hb : d152855 p = 1) : d156801 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12439 q = 1) (hb : d152855 q = 1) : d156653 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12439, d156653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30107 q ha hb
    | true =>
      simp only [d12439, d156653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12440 q = 1) (hb : d152855 q = 1) : d156654 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12440, d156654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12440, d156654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12534 q = 1) (hb : d152855 q = 1) : d156779 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12534, d156779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12534, d156779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12535 q = 1) (hb : d152855 q = 1) : d156780 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12535, d156780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12535, d156780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12536 q = 1) (hb : d152855 q = 1) : d156781 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12536, d156781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12536, d156781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12561 q = 1) (hb : d152855 q = 1) : d156801 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12561, d156801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12561, d156801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro30139 (p : Pattern) (ha : d115324 p = 1) (hb : d152855 p = 1) : d156807 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12476 q = 1) (hb : d152855 q = 1) : d156748 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12476, d156748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30121 q ha hb
    | true =>
      simp only [d12476, d156748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30122 q ha hb
  have h2 (q : Pattern) (ha : d12477 q = 1) (hb : d152855 q = 1) : d156749 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12477, d156749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12477, d156749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12478 q = 1) (hb : d152855 q = 1) : d156750 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12478, d156750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12478, d156750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12479 q = 1) (hb : d152855 q = 1) : d156751 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12479, d156751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12479, d156751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12486 q = 1) (hb : d152855 q = 1) : d156755 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12486, d156755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30123 q ha hb
    | true =>
      simp only [d12486, d156755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30124 q ha hb
  have h6 (q : Pattern) (ha : d12487 q = 1) (hb : d152855 q = 1) : d156756 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12487, d156756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12487, d156756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12488 q = 1) (hb : d152855 q = 1) : d156757 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12488, d156757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12488, d156757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12509 q = 1) (hb : d152855 q = 1) : d156777 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12509, d156777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30130 q ha hb
    | true =>
      simp only [d12509, d156777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30109 q ha hb
  have h9 (q : Pattern) (ha : d115315 q = 1) (hb : d152855 q = 1) : d156778 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115315, d156778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d115315, d156778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d12538 q = 1) (hb : d152855 q = 1) : d156783 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12538, d156783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30131 q ha hb
    | true =>
      simp only [d12538, d156783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d12539 q = 1) (hb : d152855 q = 1) : d156784 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12539, d156784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d12539, d156784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d115316 q = 1) (hb : d152855 q = 1) : d156785 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115316, d156785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d115316, d156785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d115317 q = 1) (hb : d152855 q = 1) : d156786 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115317, d156786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d115317, d156786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d115318 q = 1) (hb : d152855 q = 1) : d156787 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115318, d156787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115318, d156787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d12546 q = 1) (hb : d152855 q = 1) : d156790 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12546, d156790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30133 q ha hb
    | true =>
      simp only [d12546, d156790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30134 q ha hb
  have h16 (q : Pattern) (ha : d12547 q = 1) (hb : d152855 q = 1) : d156791 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12547, d156791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12547, d156791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d12548 q = 1) (hb : d152855 q = 1) : d156792 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12548, d156792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d12548, d156792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d12549 q = 1) (hb : d152855 q = 1) : d156793 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12549, d156793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12549, d156793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d12552 q = 1) (hb : d152855 q = 1) : d156795 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12552, d156795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30135 q ha hb
    | true =>
      simp only [d12552, d156795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30136 q ha hb
  have h20 (q : Pattern) (ha : d12553 q = 1) (hb : d152855 q = 1) : d156796 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12553, d156796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12553, d156796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d12554 q = 1) (hb : d152855 q = 1) : d156797 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12554, d156797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d12554, d156797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d12556 q = 1) (hb : d152855 q = 1) : d156799 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12556, d156799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30137 q ha hb
    | true =>
      simp only [d12556, d156799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30112 q ha hb
  have h23 (q : Pattern) (ha : d115320 q = 1) (hb : d152855 q = 1) : d156800 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115320, d156800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d115320, d156800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d12562 q = 1) (hb : d152855 q = 1) : d156802 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12562, d156802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30138 q ha hb
    | true =>
      simp only [d12562, d156802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d12563 q = 1) (hb : d152855 q = 1) : d156803 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12563, d156803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d12563, d156803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d115321 q = 1) (hb : d152855 q = 1) : d156804 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115321, d156804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d115321, d156804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d115322 q = 1) (hb : d152855 q = 1) : d156805 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115322, d156805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d115322, d156805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d115323 q = 1) (hb : d152855 q = 1) : d156806 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115323, d156806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d115323, d156806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d115324 q = 1) (hb : d152855 q = 1) : d156807 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115324, d156807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d115324, d156807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro30140 (p : Pattern) (ha : d115331 p = 1) (hb : d152855 p = 1) : d156816 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12556 q = 1) (hb : d152855 q = 1) : d156799 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12556, d156799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30137 q ha hb
    | true =>
      simp only [d12556, d156799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30112 q ha hb
  have h2 (q : Pattern) (ha : d115320 q = 1) (hb : d152855 q = 1) : d156800 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115320, d156800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115320, d156800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d12562 q = 1) (hb : d152855 q = 1) : d156802 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12562, d156802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30138 q ha hb
    | true =>
      simp only [d12562, d156802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12563 q = 1) (hb : d152855 q = 1) : d156803 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12563, d156803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12563, d156803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d115321 q = 1) (hb : d152855 q = 1) : d156804 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115321, d156804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115321, d156804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115329 q = 1) (hb : d152855 q = 1) : d156814 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115329, d156814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115329, d156814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d115330 q = 1) (hb : d152855 q = 1) : d156815 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115330, d156815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115330, d156815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d115331 q = 1) (hb : d152855 q = 1) : d156816 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115331, d156816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115331, d156816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro30141 (p : Pattern) (ha : d12595 p = 1) (hb : d152855 p = 1) : d156829 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d659 q = 1) (hb : d152854 q = 1) : d156824 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d659, d156824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d659, d156824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30125 q ha hb
  have h2 (q : Pattern) (ha : d543 q = 1) (hb : d152854 q = 1) : d156759 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d543, d156759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30125 q ha hb
    | true =>
      simp only [d543, d156759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d660 q = 1) (hb : d152854 q = 1) : d156825 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d660, d156825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d660, d156825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d544 q = 1) (hb : d152854 q = 1) : d156760 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d544, d156760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d544, d156760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d661 q = 1) (hb : d152854 q = 1) : d156826 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d661, d156826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d661, d156826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d662 q = 1) (hb : d152854 q = 1) : d156827 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d662, d156827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d662, d156827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d412 q = 1) (hb : d152854 q = 1) : d156695 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d412, d156695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d412, d156695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30088 q ha hb
  have h8 (q : Pattern) (ha : d319 q = 1) (hb : d152854 q = 1) : d156641 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319, d156641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30088 q ha hb
    | true =>
      simp only [d319, d156641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d413 q = 1) (hb : d152854 q = 1) : d156696 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d413, d156696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d413, d156696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d320 q = 1) (hb : d152854 q = 1) : d156642 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d320, d156642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d320, d156642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d414 q = 1) (hb : d152854 q = 1) : d156697 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d414, d156697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d414, d156697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d415 q = 1) (hb : d152854 q = 1) : d156698 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d415, d156698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d415, d156698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d663 q = 1) (hb : d152854 q = 1) : d156828 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d663, d156828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d663, d156828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d12595 q = 1) (hb : d152855 q = 1) : d156829 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d12595, d152855, d156829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d12595, d152855, d156829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro30142 (p : Pattern) (ha : d12604 p = 1) (hb : d152855 p = 1) : d156583 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12599 q = 1) (hb : d152854 q = 1) : d156578 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d12599, d156578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12599, d156578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30127 q ha hb
  have h2 (q : Pattern) (ha : d9382 q = 1) (hb : d152854 q = 1) : d156537 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9382, d156537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30127 q ha hb
    | true =>
      simp only [d9382, d156537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d12600 q = 1) (hb : d152854 q = 1) : d156579 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d12600, d156579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d12600, d156579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d9384 q = 1) (hb : d152854 q = 1) : d156538 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9384, d156538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9384, d156538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12601 q = 1) (hb : d152854 q = 1) : d156580 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d12601, d156580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12601, d156580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12602 q = 1) (hb : d152854 q = 1) : d156581 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d12602, d156581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12602, d156581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d66 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d66, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d66, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30048 q ha hb
  have h8 (q : Pattern) (ha : d25 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30048 q ha hb
    | true =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d67 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d67, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d67, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d26 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d68 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d68, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d68, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d69 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d69, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d69, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d12603 q = 1) (hb : d152854 q = 1) : d156582 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d12603, d156582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12603, d156582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d12604 q = 1) (hb : d152855 q = 1) : d156583 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d12604, d152855, d156583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d12604, d152855, d156583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro30143 (p : Pattern) (ha : d12610 p = 1) (hb : d152855 p = 1) : d156835 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12596 q = 1) (hb : d152855 q = 1) : d156830 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12596, d156830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30141 q ha hb
    | true =>
      simp only [d12596, d156830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30100 q ha hb
  have h2 (q : Pattern) (ha : d12597 q = 1) (hb : d152855 q = 1) : d156831 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12597, d156831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12597, d156831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12598 q = 1) (hb : d152855 q = 1) : d156832 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12598, d156832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12598, d156832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d12605 q = 1) (hb : d152855 q = 1) : d156701 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12605, d156701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30100 q ha hb
    | true =>
      simp only [d12605, d156701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30142 q ha hb
  have h5 (q : Pattern) (ha : d12606 q = 1) (hb : d152855 q = 1) : d156702 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12606, d156702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12606, d156702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12607 q = 1) (hb : d152855 q = 1) : d156703 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12607, d156703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12607, d156703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12608 q = 1) (hb : d152855 q = 1) : d156833 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12608, d156833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12608, d156833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12387 q = 1) (hb : d152855 q = 1) : d156701 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12387, d156701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30100 q ha hb
    | true =>
      simp only [d12387, d156701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30076 q ha hb
  have h9 (q : Pattern) (ha : d12388 q = 1) (hb : d152855 q = 1) : d156702 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12388, d156702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12388, d156702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d12389 q = 1) (hb : d152855 q = 1) : d156703 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12389, d156703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12389, d156703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d6079 q = 1) (hb : d152855 q = 1) : d156584 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d6079, d156584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30076 q ha hb
    | true =>
      simp only [d6079, d156584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30056 q ha hb
  have h12 (q : Pattern) (ha : d6080 q = 1) (hb : d152855 q = 1) : d156585 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d6080, d156585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6080, d156585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d6081 q = 1) (hb : d152855 q = 1) : d156586 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d6081, d156586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6081, d156586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d12390 q = 1) (hb : d152855 q = 1) : d156704 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12390, d156704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d12390, d156704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d12609 q = 1) (hb : d152855 q = 1) : d156834 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12609, d156834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12609, d156834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d12610 q = 1) (hb : d152855 q = 1) : d156835 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12610, d156835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d12610, d156835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro30144 (p : Pattern) (ha : d12614 p = 1) (hb : d152855 p = 1) : d156706 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12387 q = 1) (hb : d152855 q = 1) : d156701 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12387, d156701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30100 q ha hb
    | true =>
      simp only [d12387, d156701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30076 q ha hb
  have h2 (q : Pattern) (ha : d12388 q = 1) (hb : d152855 q = 1) : d156702 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12388, d156702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12388, d156702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12389 q = 1) (hb : d152855 q = 1) : d156703 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12389, d156703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12389, d156703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d6079 q = 1) (hb : d152855 q = 1) : d156584 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d6079, d156584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30076 q ha hb
    | true =>
      simp only [d6079, d156584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30056 q ha hb
  have h5 (q : Pattern) (ha : d6080 q = 1) (hb : d152855 q = 1) : d156585 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d6080, d156585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6080, d156585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6081 q = 1) (hb : d152855 q = 1) : d156586 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d6081, d156586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6081, d156586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12390 q = 1) (hb : d152855 q = 1) : d156704 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12390, d156704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12390, d156704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d6082 q = 1) (hb : d152855 q = 1) : d156587 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d6082, d156587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6082, d156587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d12613 q = 1) (hb : d152855 q = 1) : d156705 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12613, d156705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12613, d156705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d12614 q = 1) (hb : d152855 q = 1) : d156706 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12614, d156706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d12614, d156706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro30145 (p : Pattern) (ha : d12620 p = 1) (hb : d152855 p = 1) : d156841 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12611 q = 1) (hb : d152855 q = 1) : d156836 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12611, d156836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30143 q ha hb
    | true =>
      simp only [d12611, d156836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12612 q = 1) (hb : d152855 q = 1) : d156837 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12612, d156837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12612, d156837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12615 q = 1) (hb : d152855 q = 1) : d156707 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12615, d156707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30144 q ha hb
    | true =>
      simp only [d12615, d156707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12616 q = 1) (hb : d152855 q = 1) : d156708 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12616, d156708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12616, d156708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12617 q = 1) (hb : d152855 q = 1) : d156838 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12617, d156838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12617, d156838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12618 q = 1) (hb : d152855 q = 1) : d156839 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12618, d156839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12618, d156839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12619 q = 1) (hb : d152855 q = 1) : d156840 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12619, d156840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12619, d156840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12620 q = 1) (hb : d152855 q = 1) : d156841 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12620, d156841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12620, d156841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro30146 (p : Pattern) (ha : d12628 p = 1) (hb : d152855 p = 1) : d156712 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12615 q = 1) (hb : d152855 q = 1) : d156707 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12615, d156707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30144 q ha hb
    | true =>
      simp only [d12615, d156707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12616 q = 1) (hb : d152855 q = 1) : d156708 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12616, d156708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12616, d156708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12623 q = 1) (hb : d152855 q = 1) : d156590 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12623, d156590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30118 q ha hb
    | true =>
      simp only [d12623, d156590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12624 q = 1) (hb : d152855 q = 1) : d156591 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12624, d156591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12624, d156591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12625 q = 1) (hb : d152855 q = 1) : d156709 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12625, d156709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12625, d156709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12626 q = 1) (hb : d152855 q = 1) : d156710 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12626, d156710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12626, d156710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12627 q = 1) (hb : d152855 q = 1) : d156711 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12627, d156711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12627, d156711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12628 q = 1) (hb : d152855 q = 1) : d156712 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12628, d156712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12628, d156712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro30147 (p : Pattern) (ha : d12657 p = 1) (hb : d152855 p = 1) : d156847 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12615 q = 1) (hb : d152855 q = 1) : d156707 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12615, d156707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30144 q ha hb
    | true =>
      simp only [d12615, d156707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12616 q = 1) (hb : d152855 q = 1) : d156708 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12616, d156708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12616, d156708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12654 q = 1) (hb : d152855 q = 1) : d156844 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12654, d156844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12654, d156844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12655 q = 1) (hb : d152855 q = 1) : d156845 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12655, d156845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12655, d156845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12656 q = 1) (hb : d152855 q = 1) : d156846 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12656, d156846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12656, d156846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12657 q = 1) (hb : d152855 q = 1) : d156847 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12657, d156847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12657, d156847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro30148 (p : Pattern) (ha : d115341 p = 1) (hb : d152855 p = 1) : d156853 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12629 q = 1) (hb : d152855 q = 1) : d156842 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12629, d156842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30145 q ha hb
    | true =>
      simp only [d12629, d156842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30146 q ha hb
  have h2 (q : Pattern) (ha : d115337 q = 1) (hb : d152855 q = 1) : d156843 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115337, d156843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115337, d156843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d12658 q = 1) (hb : d152855 q = 1) : d156848 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12658, d156848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30147 q ha hb
    | true =>
      simp only [d12658, d156848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12659 q = 1) (hb : d152855 q = 1) : d156849 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12659, d156849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12659, d156849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d115338 q = 1) (hb : d152855 q = 1) : d156850 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115338, d156850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115338, d156850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115339 q = 1) (hb : d152855 q = 1) : d156851 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115339, d156851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115339, d156851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d115340 q = 1) (hb : d152855 q = 1) : d156852 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115340, d156852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115340, d156852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d115341 q = 1) (hb : d152855 q = 1) : d156853 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115341, d156853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115341, d156853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro30149 (p : Pattern) (ha : d115347 p = 1) (hb : d152855 p = 1) : d156865 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12459 q = 1) (hb : d152855 q = 1) : d156736 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12459, d156736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12459, d156736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30111 q ha hb
  have h2 (q : Pattern) (ha : d12460 q = 1) (hb : d152855 q = 1) : d156737 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d12460, d156737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d12460, d156737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d12469 q = 1) (hb : d152855 q = 1) : d156743 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12469, d156743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30111 q ha hb
    | true =>
      simp only [d12469, d156743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30114 q ha hb
  have h4 (q : Pattern) (ha : d12470 q = 1) (hb : d152855 q = 1) : d156744 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d12470, d156744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12470, d156744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12471 q = 1) (hb : d152855 q = 1) : d156745 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d12471, d156745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12471, d156745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115325 q = 1) (hb : d152855 q = 1) : d156808 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115325, d156808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30132 q ha hb
    | true =>
      simp only [d115325, d156808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30139 q ha hb
  have h7 (q : Pattern) (ha : d12581 q = 1) (hb : d152855 q = 1) : d156810 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12581, d156810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30115 q ha hb
    | true =>
      simp only [d12581, d156810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30116 q ha hb
  have h8 (q : Pattern) (ha : d115326 q = 1) (hb : d152855 q = 1) : d156811 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115326, d156811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d115326, d156811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d115327 q = 1) (hb : d152855 q = 1) : d156812 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115327, d156812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d115327, d156812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d115328 q = 1) (hb : d152855 q = 1) : d156813 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115328, d156813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d115328, d156813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d115332 q = 1) (hb : d152855 q = 1) : d156817 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115332, d156817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115332, d156817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30140 q ha hb
  have h12 (q : Pattern) (ha : d12590 q = 1) (hb : d152855 q = 1) : d156819 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12590, d156819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12590, d156819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30117 q ha hb
  have h13 (q : Pattern) (ha : d115333 q = 1) (hb : d152855 q = 1) : d156820 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115333, d156820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d115333, d156820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d115334 q = 1) (hb : d152855 q = 1) : d156821 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115334, d156821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d115334, d156821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d115335 q = 1) (hb : d152855 q = 1) : d156822 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115335, d156822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d115335, d156822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d115336 q = 1) (hb : d152855 q = 1) : d156823 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d115336, d156823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d115336, d156823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d115342 q = 1) (hb : d152855 q = 1) : d156854 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115342, d156854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115342, d156854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30148 q ha hb
  have h18 (q : Pattern) (ha : d12675 q = 1) (hb : d152855 q = 1) : d156860 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12675, d156860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12675, d156860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30120 q ha hb
  have h19 (q : Pattern) (ha : d115343 q = 1) (hb : d152855 q = 1) : d156861 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115343, d156861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d115343, d156861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d115344 q = 1) (hb : d152855 q = 1) : d156862 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115344, d156862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d115344, d156862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d115345 q = 1) (hb : d152855 q = 1) : d156863 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115345, d156863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d115345, d156863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d115346 q = 1) (hb : d152855 q = 1) : d156864 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d115346, d156864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d115346, d156864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d115347 q = 1) (hb : d152855 q = 1) : d156865 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d115347, d156865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d115347, d156865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro30150 (p : Pattern) (ha : d115353 p = 1) (hb : d152855 p = 1) : d156871 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d115348 q = 1) (hb : d152855 q = 1) : d156866 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d115348, d156866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115348, d156866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30149 q ha hb
  have h2 (q : Pattern) (ha : d115349 q = 1) (hb : d152855 q = 1) : d156867 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d115349, d156867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115349, d156867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d115350 q = 1) (hb : d152855 q = 1) : d156868 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d115350, d156868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115350, d156868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d115351 q = 1) (hb : d152855 q = 1) : d156869 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d115351, d156869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115351, d156869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d115352 q = 1) (hb : d152855 q = 1) : d156870 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d115352, d156870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115352, d156870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115353 q = 1) (hb : d152855 q = 1) : d156871 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d115353, d156871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115353, d156871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro30151 (p : Pattern) (ha : d750 p = 1) (hb : d152854 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d137 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d152852 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d750 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d750, d152854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d750, d152854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro30152 (p : Pattern) (ha : d762 p = 1) (hb : d152855 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d751 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30151 q ha hb
    | true =>
      simp only [d751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d752 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d753 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d754 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d757 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d762 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d762, d152855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d762, d152855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro30153 (p : Pattern) (ha : d4913 p = 1) (hb : d152855 p = 1) : d156874 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d319 q = 1) (hb : d152854 q = 1) : d156641 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319, d156641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30088 q ha hb
    | true =>
      simp only [d319, d156641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d320 q = 1) (hb : d152854 q = 1) : d156642 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d320, d156642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d320, d156642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d321 q = 1) (hb : d152854 q = 1) : d156643 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d321, d156643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d321, d156643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d322 q = 1) (hb : d152854 q = 1) : d156644 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d322, d156644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d322, d156644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d751 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30151 q ha hb
    | true =>
      simp only [d751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d752 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d753 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d754 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d755 q = 1) (hb : d152854 q = 1) : d156873 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d755, d156873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d755, d156873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d4913 q = 1) (hb : d152855 q = 1) : d156874 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d4913, d152855, d156874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d4913, d152855, d156874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro30154 (p : Pattern) (ha : d12693 p = 1) (hb : d152855 p = 1) : d156884 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12688 q = 1) (hb : d152855 q = 1) : d156875 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12688, d156875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30126 q ha hb
    | true =>
      simp only [d12688, d156875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30153 q ha hb
  have h2 (q : Pattern) (ha : d12689 q = 1) (hb : d152855 q = 1) : d156876 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12689, d156876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12689, d156876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12690 q = 1) (hb : d152855 q = 1) : d156877 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12690, d156877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12690, d156877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d4914 q = 1) (hb : d152855 q = 1) : d156878 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d4914, d156878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30153 q ha hb
    | true =>
      simp only [d4914, d156878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30152 q ha hb
  have h5 (q : Pattern) (ha : d4915 q = 1) (hb : d152855 q = 1) : d156879 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d4915, d156879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4915, d156879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4916 q = 1) (hb : d152855 q = 1) : d156880 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d4916, d156880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4916, d156880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12691 q = 1) (hb : d152855 q = 1) : d156881 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12691, d156881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12691, d156881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d4917 q = 1) (hb : d152855 q = 1) : d156882 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d4917, d156882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d4917, d156882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d12692 q = 1) (hb : d152855 q = 1) : d156883 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12692, d156883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12692, d156883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d12693 q = 1) (hb : d152855 q = 1) : d156884 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12693, d156884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d12693, d156884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro30155 (p : Pattern) (ha : d12697 p = 1) (hb : d152855 p = 1) : d156888 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4914 q = 1) (hb : d152855 q = 1) : d156878 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d4914, d156878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30153 q ha hb
    | true =>
      simp only [d4914, d156878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30152 q ha hb
  have h2 (q : Pattern) (ha : d4915 q = 1) (hb : d152855 q = 1) : d156879 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d4915, d156879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4915, d156879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d4916 q = 1) (hb : d152855 q = 1) : d156880 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d4916, d156880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4916, d156880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d4917 q = 1) (hb : d152855 q = 1) : d156882 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d4917, d156882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4917, d156882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12696 q = 1) (hb : d152855 q = 1) : d156887 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12696, d156887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12696, d156887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12697 q = 1) (hb : d152855 q = 1) : d156888 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12697, d156888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12697, d156888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro30156 (p : Pattern) (ha : d12703 p = 1) (hb : d152855 p = 1) : d156894 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12694 q = 1) (hb : d152855 q = 1) : d156885 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12694, d156885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30154 q ha hb
    | true =>
      simp only [d12694, d156885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12695 q = 1) (hb : d152855 q = 1) : d156886 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12695, d156886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12695, d156886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12698 q = 1) (hb : d152855 q = 1) : d156889 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12698, d156889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30155 q ha hb
    | true =>
      simp only [d12698, d156889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12699 q = 1) (hb : d152855 q = 1) : d156890 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12699, d156890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12699, d156890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12700 q = 1) (hb : d152855 q = 1) : d156891 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12700, d156891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12700, d156891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12701 q = 1) (hb : d152855 q = 1) : d156892 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12701, d156892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12701, d156892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12702 q = 1) (hb : d152855 q = 1) : d156893 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12702, d156893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12702, d156893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12703 q = 1) (hb : d152855 q = 1) : d156894 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12703, d156894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12703, d156894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro30157 (p : Pattern) (ha : d12707 p = 1) (hb : d152855 p = 1) : d156898 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12698 q = 1) (hb : d152855 q = 1) : d156889 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12698, d156889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30155 q ha hb
    | true =>
      simp only [d12698, d156889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12699 q = 1) (hb : d152855 q = 1) : d156890 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12699, d156890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12699, d156890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12704 q = 1) (hb : d152855 q = 1) : d156895 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12704, d156895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12704, d156895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12705 q = 1) (hb : d152855 q = 1) : d156896 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12705, d156896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12705, d156896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12706 q = 1) (hb : d152855 q = 1) : d156897 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12706, d156897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12706, d156897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12707 q = 1) (hb : d152855 q = 1) : d156898 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12707, d156898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12707, d156898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro30158 (p : Pattern) (ha : d12713 p = 1) (hb : d152855 p = 1) : d156904 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12708 q = 1) (hb : d152855 q = 1) : d156899 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12708, d156899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30156 q ha hb
    | true =>
      simp only [d12708, d156899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30157 q ha hb
  have h2 (q : Pattern) (ha : d12709 q = 1) (hb : d152855 q = 1) : d156900 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12709, d156900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12709, d156900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12710 q = 1) (hb : d152855 q = 1) : d156901 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12710, d156901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12710, d156901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12711 q = 1) (hb : d152855 q = 1) : d156902 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12711, d156902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12711, d156902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12712 q = 1) (hb : d152855 q = 1) : d156903 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12712, d156903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12712, d156903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12713 q = 1) (hb : d152855 q = 1) : d156904 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d12713, d156904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12713, d156904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro30159 (p : Pattern) (ha : d12716 p = 1) (hb : d152855 p = 1) : d156907 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12694 q = 1) (hb : d152855 q = 1) : d156885 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12694, d156885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30154 q ha hb
    | true =>
      simp only [d12694, d156885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12695 q = 1) (hb : d152855 q = 1) : d156886 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12695, d156886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12695, d156886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12698 q = 1) (hb : d152855 q = 1) : d156889 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12698, d156889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30155 q ha hb
    | true =>
      simp only [d12698, d156889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12699 q = 1) (hb : d152855 q = 1) : d156890 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12699, d156890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12699, d156890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12700 q = 1) (hb : d152855 q = 1) : d156891 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12700, d156891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12700, d156891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12701 q = 1) (hb : d152855 q = 1) : d156892 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12701, d156892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12701, d156892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12702 q = 1) (hb : d152855 q = 1) : d156893 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12702, d156893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12702, d156893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12716 q = 1) (hb : d152855 q = 1) : d156907 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12716, d156907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12716, d156907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro30160 (p : Pattern) (ha : d12717 p = 1) (hb : d152855 p = 1) : d156908 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12698 q = 1) (hb : d152855 q = 1) : d156889 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12698, d156889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30155 q ha hb
    | true =>
      simp only [d12698, d156889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12699 q = 1) (hb : d152855 q = 1) : d156890 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12699, d156890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12699, d156890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12704 q = 1) (hb : d152855 q = 1) : d156895 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12704, d156895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12704, d156895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12705 q = 1) (hb : d152855 q = 1) : d156896 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12705, d156896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12705, d156896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12706 q = 1) (hb : d152855 q = 1) : d156897 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12706, d156897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12706, d156897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12717 q = 1) (hb : d152855 q = 1) : d156908 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12717, d156908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12717, d156908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro30161 (p : Pattern) (ha : d12723 p = 1) (hb : d152855 p = 1) : d156914 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12708 q = 1) (hb : d152855 q = 1) : d156899 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12708, d156899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30156 q ha hb
    | true =>
      simp only [d12708, d156899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30157 q ha hb
  have h2 (q : Pattern) (ha : d12709 q = 1) (hb : d152855 q = 1) : d156900 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12709, d156900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12709, d156900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12710 q = 1) (hb : d152855 q = 1) : d156901 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12710, d156901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12710, d156901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12711 q = 1) (hb : d152855 q = 1) : d156902 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12711, d156902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12711, d156902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12712 q = 1) (hb : d152855 q = 1) : d156903 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12712, d156903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12712, d156903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12718 q = 1) (hb : d152855 q = 1) : d156909 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12718, d156909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30159 q ha hb
    | true =>
      simp only [d12718, d156909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30160 q ha hb
  have h7 (q : Pattern) (ha : d12719 q = 1) (hb : d152855 q = 1) : d156910 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12719, d156910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12719, d156910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12720 q = 1) (hb : d152855 q = 1) : d156911 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12720, d156911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12720, d156911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d12721 q = 1) (hb : d152855 q = 1) : d156912 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12721, d156912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12721, d156912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d12722 q = 1) (hb : d152855 q = 1) : d156913 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12722, d156913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12722, d156913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d12723 q = 1) (hb : d152855 q = 1) : d156914 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d12723, d156914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12723, d156914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro30162 (p : Pattern) (ha : d12833 p = 1) (hb : d152855 p = 1) : d157005 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12708 q = 1) (hb : d152855 q = 1) : d156899 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12708, d156899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30156 q ha hb
    | true =>
      simp only [d12708, d156899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30157 q ha hb
  have h2 (q : Pattern) (ha : d12709 q = 1) (hb : d152855 q = 1) : d156900 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12709, d156900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12709, d156900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12710 q = 1) (hb : d152855 q = 1) : d156901 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12710, d156901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12710, d156901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12711 q = 1) (hb : d152855 q = 1) : d156902 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12711, d156902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12711, d156902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12712 q = 1) (hb : d152855 q = 1) : d156903 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12712, d156903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12712, d156903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12828 q = 1) (hb : d152855 q = 1) : d157000 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12828, d157000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30157 q ha hb
    | true =>
      simp only [d12828, d157000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12829 q = 1) (hb : d152855 q = 1) : d157001 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12829, d157001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12829, d157001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12830 q = 1) (hb : d152855 q = 1) : d157002 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12830, d157002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12830, d157002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d12831 q = 1) (hb : d152855 q = 1) : d157003 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12831, d157003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12831, d157003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d12832 q = 1) (hb : d152855 q = 1) : d157004 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12832, d157004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12832, d157004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d12833 q = 1) (hb : d152855 q = 1) : d157005 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d12833, d157005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12833, d157005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro30163 (p : Pattern) (ha : d12839 p = 1) (hb : d152855 p = 1) : d157011 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12828 q = 1) (hb : d152855 q = 1) : d157000 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12828, d157000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30157 q ha hb
    | true =>
      simp only [d12828, d157000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12829 q = 1) (hb : d152855 q = 1) : d157001 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12829, d157001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12829, d157001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12830 q = 1) (hb : d152855 q = 1) : d157002 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12830, d157002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12830, d157002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12831 q = 1) (hb : d152855 q = 1) : d157003 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12831, d157003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12831, d157003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12832 q = 1) (hb : d152855 q = 1) : d157004 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12832, d157004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12832, d157004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12834 q = 1) (hb : d152855 q = 1) : d157006 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12834, d157006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30160 q ha hb
    | true =>
      simp only [d12834, d157006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12835 q = 1) (hb : d152855 q = 1) : d157007 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12835, d157007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12835, d157007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12836 q = 1) (hb : d152855 q = 1) : d157008 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12836, d157008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12836, d157008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d12837 q = 1) (hb : d152855 q = 1) : d157009 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12837, d157009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12837, d157009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d12838 q = 1) (hb : d152855 q = 1) : d157010 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12838, d157010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12838, d157010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d12839 q = 1) (hb : d152855 q = 1) : d157011 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d12839, d157011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12839, d157011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro30164 (p : Pattern) (ha : d12848 p = 1) (hb : d152855 p = 1) : d157020 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12834 q = 1) (hb : d152855 q = 1) : d157006 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12834, d157006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30160 q ha hb
    | true =>
      simp only [d12834, d157006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12835 q = 1) (hb : d152855 q = 1) : d157007 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12835, d157007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12835, d157007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12836 q = 1) (hb : d152855 q = 1) : d157008 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12836, d157008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12836, d157008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12837 q = 1) (hb : d152855 q = 1) : d157009 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12837, d157009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12837, d157009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12838 q = 1) (hb : d152855 q = 1) : d157010 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12838, d157010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12838, d157010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12848 q = 1) (hb : d152855 q = 1) : d157020 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d12848, d157020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12848, d157020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro30165 (p : Pattern) (ha : d986 p = 1) (hb : d152855 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d971 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30151 q ha hb
  have h2 (q : Pattern) (ha : d751 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30151 q ha hb
    | true =>
      simp only [d751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d972 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d752 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d973 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d974 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d980 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d986 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d986, d152855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d986, d152855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro30166 (p : Pattern) (ha : d6210 p = 1) (hb : d152855 p = 1) : d157046 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d412 q = 1) (hb : d152854 q = 1) : d156695 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d412, d156695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d412, d156695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30088 q ha hb
  have h2 (q : Pattern) (ha : d319 q = 1) (hb : d152854 q = 1) : d156641 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319, d156641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30088 q ha hb
    | true =>
      simp only [d319, d156641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d413 q = 1) (hb : d152854 q = 1) : d156696 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d413, d156696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d413, d156696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d320 q = 1) (hb : d152854 q = 1) : d156642 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d320, d156642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d320, d156642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d414 q = 1) (hb : d152854 q = 1) : d156697 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d414, d156697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d414, d156697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d415 q = 1) (hb : d152854 q = 1) : d156698 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d415, d156698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d415, d156698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d971 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30151 q ha hb
  have h8 (q : Pattern) (ha : d751 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30151 q ha hb
    | true =>
      simp only [d751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d972 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d752 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d973 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d974 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d975 q = 1) (hb : d152854 q = 1) : d157045 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d975, d157045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d975, d157045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d6210 q = 1) (hb : d152855 q = 1) : d157046 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d6210, d152855, d157046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d6210, d152855, d157046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro30167 (p : Pattern) (ha : d12885 p = 1) (hb : d152855 p = 1) : d157068 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6211 q = 1) (hb : d152855 q = 1) : d157050 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d6211, d157050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30166 q ha hb
    | true =>
      simp only [d6211, d157050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30165 q ha hb
  have h2 (q : Pattern) (ha : d6212 q = 1) (hb : d152855 q = 1) : d157051 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d6212, d157051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6212, d157051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6213 q = 1) (hb : d152855 q = 1) : d157052 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d6213, d157052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6213, d157052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d6214 q = 1) (hb : d152855 q = 1) : d157058 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d6214, d157058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6214, d157058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12884 q = 1) (hb : d152855 q = 1) : d157067 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12884, d157067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12884, d157067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12885 q = 1) (hb : d152855 q = 1) : d157068 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12885, d157068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12885, d157068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro30168 (p : Pattern) (ha : d12935 p = 1) (hb : d152855 p = 1) : d157091 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12886 q = 1) (hb : d152855 q = 1) : d157069 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12886, d157069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30167 q ha hb
    | true =>
      simp only [d12886, d157069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12887 q = 1) (hb : d152855 q = 1) : d157070 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12887, d157070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12887, d157070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12932 q = 1) (hb : d152855 q = 1) : d157088 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12932, d157088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12932, d157088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12933 q = 1) (hb : d152855 q = 1) : d157089 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12933, d157089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12933, d157089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12934 q = 1) (hb : d152855 q = 1) : d157090 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12934, d157090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12934, d157090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12935 q = 1) (hb : d152855 q = 1) : d157091 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12935, d157091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12935, d157091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro30169 (p : Pattern) (ha : d12941 p = 1) (hb : d152855 p = 1) : d157097 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12936 q = 1) (hb : d152855 q = 1) : d157092 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12936, d157092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30168 q ha hb
    | true =>
      simp only [d12936, d157092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12937 q = 1) (hb : d152855 q = 1) : d157093 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12937, d157093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12937, d157093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12938 q = 1) (hb : d152855 q = 1) : d157094 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12938, d157094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12938, d157094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12939 q = 1) (hb : d152855 q = 1) : d157095 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12939, d157095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12939, d157095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12940 q = 1) (hb : d152855 q = 1) : d157096 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12940, d157096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12940, d157096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12941 q = 1) (hb : d152855 q = 1) : d157097 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d12941, d157097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12941, d157097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro30170 (p : Pattern) (ha : d12728 p = 1) (hb : d152855 p = 1) : d156919 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12694 q = 1) (hb : d152855 q = 1) : d156885 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12694, d156885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30154 q ha hb
    | true =>
      simp only [d12694, d156885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12695 q = 1) (hb : d152855 q = 1) : d156886 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12695, d156886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12695, d156886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12698 q = 1) (hb : d152855 q = 1) : d156889 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12698, d156889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30155 q ha hb
    | true =>
      simp only [d12698, d156889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12699 q = 1) (hb : d152855 q = 1) : d156890 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12699, d156890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12699, d156890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12700 q = 1) (hb : d152855 q = 1) : d156891 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12700, d156891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12700, d156891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12701 q = 1) (hb : d152855 q = 1) : d156892 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12701, d156892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12701, d156892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12727 q = 1) (hb : d152855 q = 1) : d156918 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12727, d156918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12727, d156918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12728 q = 1) (hb : d152855 q = 1) : d156919 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12728, d156919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12728, d156919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro30171 (p : Pattern) (ha : d12730 p = 1) (hb : d152855 p = 1) : d156921 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12698 q = 1) (hb : d152855 q = 1) : d156889 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12698, d156889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30155 q ha hb
    | true =>
      simp only [d12698, d156889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12699 q = 1) (hb : d152855 q = 1) : d156890 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12699, d156890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12699, d156890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12704 q = 1) (hb : d152855 q = 1) : d156895 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12704, d156895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12704, d156895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12705 q = 1) (hb : d152855 q = 1) : d156896 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12705, d156896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12705, d156896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12729 q = 1) (hb : d152855 q = 1) : d156920 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12729, d156920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12729, d156920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12730 q = 1) (hb : d152855 q = 1) : d156921 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12730, d156921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12730, d156921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro30172 (p : Pattern) (ha : d12737 p = 1) (hb : d152855 p = 1) : d156928 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12694 q = 1) (hb : d152855 q = 1) : d156885 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12694, d156885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30154 q ha hb
    | true =>
      simp only [d12694, d156885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12695 q = 1) (hb : d152855 q = 1) : d156886 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12695, d156886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12695, d156886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12698 q = 1) (hb : d152855 q = 1) : d156889 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12698, d156889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30155 q ha hb
    | true =>
      simp only [d12698, d156889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12699 q = 1) (hb : d152855 q = 1) : d156890 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12699, d156890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12699, d156890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12700 q = 1) (hb : d152855 q = 1) : d156891 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12700, d156891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12700, d156891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12735 q = 1) (hb : d152855 q = 1) : d156926 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12735, d156926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12735, d156926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12736 q = 1) (hb : d152855 q = 1) : d156927 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12736, d156927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12736, d156927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12737 q = 1) (hb : d152855 q = 1) : d156928 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12737, d156928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12737, d156928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro30173 (p : Pattern) (ha : d12740 p = 1) (hb : d152855 p = 1) : d156931 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12698 q = 1) (hb : d152855 q = 1) : d156889 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12698, d156889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30155 q ha hb
    | true =>
      simp only [d12698, d156889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12699 q = 1) (hb : d152855 q = 1) : d156890 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12699, d156890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12699, d156890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12704 q = 1) (hb : d152855 q = 1) : d156895 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12704, d156895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12704, d156895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12738 q = 1) (hb : d152855 q = 1) : d156929 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12738, d156929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12738, d156929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12739 q = 1) (hb : d152855 q = 1) : d156930 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12739, d156930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12739, d156930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12740 q = 1) (hb : d152855 q = 1) : d156931 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12740, d156931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12740, d156931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro30174 (p : Pattern) (ha : d833 p = 1) (hb : d152854 p = 1) : d156935 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d532 q = 1) : d532 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d314 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d533 q = 1) (hb : d152852 q = 1) : d25428 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d533, d152852, d25428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d533, d152852, d25428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d1 q = 1) (hb : d538 q = 1) : d538 q = 1 := by
    exact hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d134 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d539 q = 1) (hb : d152852 q = 1) : d25429 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d539, d152852, d25429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d539, d152852, d25429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d540 q = 1) (hb : d152852 q = 1) : d25430 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d540, d25430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d540, d25430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d152852 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d541 q = 1) (hb : d152852 q = 1) : d25431 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d541, d25431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d541, d25431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d833 q = 1) (hb : d152854 q = 1) : d156935 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d833, d152854, d156935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d833, d152854, d156935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro30175 (p : Pattern) (ha : d12744 p = 1) (hb : d152855 p = 1) : d156941 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d834 q = 1) (hb : d152854 q = 1) : d156936 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d834, d156936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30174 q ha hb
    | true =>
      simp only [d834, d156936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d835 q = 1) (hb : d152854 q = 1) : d156937 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d835, d156937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d835, d156937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d836 q = 1) (hb : d152854 q = 1) : d156938 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d836, d156938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d836, d156938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d837 q = 1) (hb : d152854 q = 1) : d156939 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d837, d156939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d837, d156939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d543 q = 1) (hb : d152854 q = 1) : d156759 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d543, d156759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30125 q ha hb
    | true =>
      simp only [d543, d156759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d544 q = 1) (hb : d152854 q = 1) : d156760 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d544, d156760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d544, d156760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d545 q = 1) (hb : d152854 q = 1) : d156761 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d545, d156761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d545, d156761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d546 q = 1) (hb : d152854 q = 1) : d156762 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d546, d156762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d546, d156762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d838 q = 1) (hb : d152854 q = 1) : d156940 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d838, d156940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d838, d156940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d12744 q = 1) (hb : d152855 q = 1) : d156941 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d12744, d152855, d156941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d12744, d152855, d156941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro30176 (p : Pattern) (ha : d9467 p = 1) (hb : d152854 p = 1) : d156947 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d9466 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d9453 q = 1) : d9453 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d20 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d9454 q = 1) (hb : d152852 q = 1) : d37008 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d9454, d152852, d37008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d9454, d152852, d37008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d152852 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d9455 q = 1) (hb : d152852 q = 1) : d156945 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d9455, d156945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9455, d156945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d9456 q = 1) (hb : d152852 q = 1) : d156946 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d9456, d156946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9456, d156946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h7 (q : Pattern) (ha : d9467 q = 1) (hb : d152854 q = 1) : d156947 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d9467, d152854, d156947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d9467, d152854, d156947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro30177 (p : Pattern) (ha : d12751 p = 1) (hb : d152855 p = 1) : d156953 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9468 q = 1) (hb : d152854 q = 1) : d156948 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9468, d156948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30176 q ha hb
    | true =>
      simp only [d9468, d156948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9470 q = 1) (hb : d152854 q = 1) : d156949 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9470, d156949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d9470, d156949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d12748 q = 1) (hb : d152854 q = 1) : d156950 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d12748, d156950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12748, d156950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d12749 q = 1) (hb : d152854 q = 1) : d156951 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d12749, d156951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12749, d156951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d751 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30151 q ha hb
    | true =>
      simp only [d751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d752 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d753 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d754 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d12750 q = 1) (hb : d152854 q = 1) : d156952 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d12750, d156952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12750, d156952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d12751 q = 1) (hb : d152855 q = 1) : d156953 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d12751, d152855, d156953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d12751, d152855, d156953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro30178 (p : Pattern) (ha : d12757 p = 1) (hb : d152855 p = 1) : d156959 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12745 q = 1) (hb : d152855 q = 1) : d156942 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12745, d156942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30175 q ha hb
    | true =>
      simp only [d12745, d156942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30126 q ha hb
  have h2 (q : Pattern) (ha : d12746 q = 1) (hb : d152855 q = 1) : d156943 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12746, d156943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12746, d156943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12747 q = 1) (hb : d152855 q = 1) : d156944 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12747, d156944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12747, d156944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d12752 q = 1) (hb : d152855 q = 1) : d156954 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12752, d156954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30126 q ha hb
    | true =>
      simp only [d12752, d156954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30177 q ha hb
  have h5 (q : Pattern) (ha : d12753 q = 1) (hb : d152855 q = 1) : d156955 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12753, d156955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12753, d156955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12754 q = 1) (hb : d152855 q = 1) : d156956 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12754, d156956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12754, d156956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12755 q = 1) (hb : d152855 q = 1) : d156957 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12755, d156957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12755, d156957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12688 q = 1) (hb : d152855 q = 1) : d156875 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12688, d156875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30126 q ha hb
    | true =>
      simp only [d12688, d156875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30153 q ha hb
  have h9 (q : Pattern) (ha : d12689 q = 1) (hb : d152855 q = 1) : d156876 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12689, d156876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12689, d156876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d12690 q = 1) (hb : d152855 q = 1) : d156877 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12690, d156877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12690, d156877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d4914 q = 1) (hb : d152855 q = 1) : d156878 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d4914, d156878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30153 q ha hb
    | true =>
      simp only [d4914, d156878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30152 q ha hb
  have h12 (q : Pattern) (ha : d4915 q = 1) (hb : d152855 q = 1) : d156879 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d4915, d156879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4915, d156879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d4916 q = 1) (hb : d152855 q = 1) : d156880 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d4916, d156880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4916, d156880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d12691 q = 1) (hb : d152855 q = 1) : d156881 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12691, d156881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d12691, d156881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d12756 q = 1) (hb : d152855 q = 1) : d156958 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12756, d156958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12756, d156958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d12757 q = 1) (hb : d152855 q = 1) : d156959 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12757, d156959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d12757, d156959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro30179 (p : Pattern) (ha : d12763 p = 1) (hb : d152855 p = 1) : d156965 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12758 q = 1) (hb : d152855 q = 1) : d156960 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12758, d156960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30178 q ha hb
    | true =>
      simp only [d12758, d156960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12759 q = 1) (hb : d152855 q = 1) : d156961 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12759, d156961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12759, d156961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12694 q = 1) (hb : d152855 q = 1) : d156885 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12694, d156885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30154 q ha hb
    | true =>
      simp only [d12694, d156885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12695 q = 1) (hb : d152855 q = 1) : d156886 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12695, d156886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12695, d156886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12760 q = 1) (hb : d152855 q = 1) : d156962 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12760, d156962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12760, d156962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12761 q = 1) (hb : d152855 q = 1) : d156963 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12761, d156963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12761, d156963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12762 q = 1) (hb : d152855 q = 1) : d156964 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12762, d156964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12762, d156964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12763 q = 1) (hb : d152855 q = 1) : d156965 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12763, d156965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12763, d156965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro30180 (p : Pattern) (ha : d12796 p = 1) (hb : d152855 p = 1) : d156971 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12694 q = 1) (hb : d152855 q = 1) : d156885 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12694, d156885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30154 q ha hb
    | true =>
      simp only [d12694, d156885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12695 q = 1) (hb : d152855 q = 1) : d156886 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12695, d156886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12695, d156886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12793 q = 1) (hb : d152855 q = 1) : d156968 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12793, d156968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12793, d156968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12794 q = 1) (hb : d152855 q = 1) : d156969 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12794, d156969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12794, d156969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12795 q = 1) (hb : d152855 q = 1) : d156970 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12795, d156970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12795, d156970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12796 q = 1) (hb : d152855 q = 1) : d156971 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12796, d156971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12796, d156971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro30181 (p : Pattern) (ha : d115359 p = 1) (hb : d152855 p = 1) : d156977 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12731 q = 1) (hb : d152855 q = 1) : d156922 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12731, d156922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30170 q ha hb
    | true =>
      simp only [d12731, d156922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30171 q ha hb
  have h2 (q : Pattern) (ha : d12732 q = 1) (hb : d152855 q = 1) : d156923 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12732, d156923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12732, d156923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12733 q = 1) (hb : d152855 q = 1) : d156924 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12733, d156924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12733, d156924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12734 q = 1) (hb : d152855 q = 1) : d156925 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12734, d156925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12734, d156925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12741 q = 1) (hb : d152855 q = 1) : d156932 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12741, d156932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30172 q ha hb
    | true =>
      simp only [d12741, d156932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30173 q ha hb
  have h6 (q : Pattern) (ha : d12742 q = 1) (hb : d152855 q = 1) : d156933 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12742, d156933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12742, d156933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12743 q = 1) (hb : d152855 q = 1) : d156934 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12743, d156934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12743, d156934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12764 q = 1) (hb : d152855 q = 1) : d156966 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12764, d156966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30179 q ha hb
    | true =>
      simp only [d12764, d156966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30156 q ha hb
  have h9 (q : Pattern) (ha : d115355 q = 1) (hb : d152855 q = 1) : d156967 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115355, d156967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d115355, d156967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d12797 q = 1) (hb : d152855 q = 1) : d156972 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12797, d156972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30180 q ha hb
    | true =>
      simp only [d12797, d156972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d12798 q = 1) (hb : d152855 q = 1) : d156973 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12798, d156973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d12798, d156973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d115356 q = 1) (hb : d152855 q = 1) : d156974 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115356, d156974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d115356, d156974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d115357 q = 1) (hb : d152855 q = 1) : d156975 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115357, d156975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d115357, d156975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d115358 q = 1) (hb : d152855 q = 1) : d156976 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115358, d156976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115358, d156976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d115359 q = 1) (hb : d152855 q = 1) : d156977 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115359, d156977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115359, d156977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro30182 (p : Pattern) (ha : d12803 p = 1) (hb : d152855 p = 1) : d156978 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12694 q = 1) (hb : d152855 q = 1) : d156885 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12694, d156885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30154 q ha hb
    | true =>
      simp only [d12694, d156885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12695 q = 1) (hb : d152855 q = 1) : d156886 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12695, d156886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12695, d156886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12698 q = 1) (hb : d152855 q = 1) : d156889 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12698, d156889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30155 q ha hb
    | true =>
      simp only [d12698, d156889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12699 q = 1) (hb : d152855 q = 1) : d156890 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12699, d156890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12699, d156890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12700 q = 1) (hb : d152855 q = 1) : d156891 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12700, d156891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12700, d156891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12701 q = 1) (hb : d152855 q = 1) : d156892 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12701, d156892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12701, d156892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12727 q = 1) (hb : d152855 q = 1) : d156918 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12727, d156918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12727, d156918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12803 q = 1) (hb : d152855 q = 1) : d156978 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12803, d156978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12803, d156978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro30183 (p : Pattern) (ha : d12804 p = 1) (hb : d152855 p = 1) : d156979 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12698 q = 1) (hb : d152855 q = 1) : d156889 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12698, d156889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30155 q ha hb
    | true =>
      simp only [d12698, d156889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12699 q = 1) (hb : d152855 q = 1) : d156890 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12699, d156890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12699, d156890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12704 q = 1) (hb : d152855 q = 1) : d156895 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12704, d156895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12704, d156895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12705 q = 1) (hb : d152855 q = 1) : d156896 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12705, d156896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12705, d156896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12729 q = 1) (hb : d152855 q = 1) : d156920 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12729, d156920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12729, d156920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12804 q = 1) (hb : d152855 q = 1) : d156979 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12804, d156979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12804, d156979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro30184 (p : Pattern) (ha : d12809 p = 1) (hb : d152855 p = 1) : d156984 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12694 q = 1) (hb : d152855 q = 1) : d156885 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12694, d156885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30154 q ha hb
    | true =>
      simp only [d12694, d156885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12695 q = 1) (hb : d152855 q = 1) : d156886 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12695, d156886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12695, d156886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12698 q = 1) (hb : d152855 q = 1) : d156889 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12698, d156889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30155 q ha hb
    | true =>
      simp only [d12698, d156889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12699 q = 1) (hb : d152855 q = 1) : d156890 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12699, d156890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12699, d156890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12700 q = 1) (hb : d152855 q = 1) : d156891 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12700, d156891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12700, d156891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12735 q = 1) (hb : d152855 q = 1) : d156926 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12735, d156926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12735, d156926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12736 q = 1) (hb : d152855 q = 1) : d156927 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12736, d156927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12736, d156927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12809 q = 1) (hb : d152855 q = 1) : d156984 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12809, d156984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12809, d156984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro30185 (p : Pattern) (ha : d12810 p = 1) (hb : d152855 p = 1) : d156985 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12698 q = 1) (hb : d152855 q = 1) : d156889 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12698, d156889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30155 q ha hb
    | true =>
      simp only [d12698, d156889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12699 q = 1) (hb : d152855 q = 1) : d156890 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12699, d156890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12699, d156890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12704 q = 1) (hb : d152855 q = 1) : d156895 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12704, d156895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12704, d156895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12738 q = 1) (hb : d152855 q = 1) : d156929 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12738, d156929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12738, d156929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12739 q = 1) (hb : d152855 q = 1) : d156930 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12739, d156930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12739, d156930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12810 q = 1) (hb : d152855 q = 1) : d156985 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12810, d156985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12810, d156985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro30186 (p : Pattern) (ha : d12814 p = 1) (hb : d152855 p = 1) : d156989 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12758 q = 1) (hb : d152855 q = 1) : d156960 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12758, d156960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30178 q ha hb
    | true =>
      simp only [d12758, d156960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12759 q = 1) (hb : d152855 q = 1) : d156961 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12759, d156961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12759, d156961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12694 q = 1) (hb : d152855 q = 1) : d156885 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12694, d156885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30154 q ha hb
    | true =>
      simp only [d12694, d156885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12695 q = 1) (hb : d152855 q = 1) : d156886 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12695, d156886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12695, d156886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12760 q = 1) (hb : d152855 q = 1) : d156962 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12760, d156962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12760, d156962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12761 q = 1) (hb : d152855 q = 1) : d156963 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12761, d156963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12761, d156963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12762 q = 1) (hb : d152855 q = 1) : d156964 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12762, d156964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12762, d156964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12814 q = 1) (hb : d152855 q = 1) : d156989 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12814, d156989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12814, d156989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro30187 (p : Pattern) (ha : d12820 p = 1) (hb : d152855 p = 1) : d156992 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12694 q = 1) (hb : d152855 q = 1) : d156885 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12694, d156885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30154 q ha hb
    | true =>
      simp only [d12694, d156885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12695 q = 1) (hb : d152855 q = 1) : d156886 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12695, d156886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12695, d156886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12793 q = 1) (hb : d152855 q = 1) : d156968 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12793, d156968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12793, d156968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12794 q = 1) (hb : d152855 q = 1) : d156969 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12794, d156969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12794, d156969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12795 q = 1) (hb : d152855 q = 1) : d156970 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12795, d156970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12795, d156970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12820 q = 1) (hb : d152855 q = 1) : d156992 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12820, d156992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12820, d156992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro30188 (p : Pattern) (ha : d115364 p = 1) (hb : d152855 p = 1) : d156998 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12731 q = 1) (hb : d152855 q = 1) : d156922 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12731, d156922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30170 q ha hb
    | true =>
      simp only [d12731, d156922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30171 q ha hb
  have h2 (q : Pattern) (ha : d12732 q = 1) (hb : d152855 q = 1) : d156923 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12732, d156923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12732, d156923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12733 q = 1) (hb : d152855 q = 1) : d156924 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12733, d156924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12733, d156924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12734 q = 1) (hb : d152855 q = 1) : d156925 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12734, d156925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12734, d156925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12741 q = 1) (hb : d152855 q = 1) : d156932 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12741, d156932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30172 q ha hb
    | true =>
      simp only [d12741, d156932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30173 q ha hb
  have h6 (q : Pattern) (ha : d12742 q = 1) (hb : d152855 q = 1) : d156933 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12742, d156933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12742, d156933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12743 q = 1) (hb : d152855 q = 1) : d156934 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12743, d156934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12743, d156934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12764 q = 1) (hb : d152855 q = 1) : d156966 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12764, d156966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30179 q ha hb
    | true =>
      simp only [d12764, d156966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30156 q ha hb
  have h9 (q : Pattern) (ha : d115355 q = 1) (hb : d152855 q = 1) : d156967 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115355, d156967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d115355, d156967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d12797 q = 1) (hb : d152855 q = 1) : d156972 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12797, d156972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30180 q ha hb
    | true =>
      simp only [d12797, d156972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d12798 q = 1) (hb : d152855 q = 1) : d156973 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12798, d156973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d12798, d156973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d115356 q = 1) (hb : d152855 q = 1) : d156974 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115356, d156974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d115356, d156974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d115357 q = 1) (hb : d152855 q = 1) : d156975 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115357, d156975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d115357, d156975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d115358 q = 1) (hb : d152855 q = 1) : d156976 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115358, d156976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115358, d156976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d12805 q = 1) (hb : d152855 q = 1) : d156980 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12805, d156980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30182 q ha hb
    | true =>
      simp only [d12805, d156980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30183 q ha hb
  have h16 (q : Pattern) (ha : d12806 q = 1) (hb : d152855 q = 1) : d156981 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12806, d156981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12806, d156981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d12807 q = 1) (hb : d152855 q = 1) : d156982 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12807, d156982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d12807, d156982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d12808 q = 1) (hb : d152855 q = 1) : d156983 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12808, d156983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12808, d156983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d12811 q = 1) (hb : d152855 q = 1) : d156986 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12811, d156986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30184 q ha hb
    | true =>
      simp only [d12811, d156986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30185 q ha hb
  have h20 (q : Pattern) (ha : d12812 q = 1) (hb : d152855 q = 1) : d156987 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12812, d156987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12812, d156987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d12813 q = 1) (hb : d152855 q = 1) : d156988 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12813, d156988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d12813, d156988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d12815 q = 1) (hb : d152855 q = 1) : d156990 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12815, d156990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30186 q ha hb
    | true =>
      simp only [d12815, d156990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30159 q ha hb
  have h23 (q : Pattern) (ha : d115360 q = 1) (hb : d152855 q = 1) : d156991 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115360, d156991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d115360, d156991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d12821 q = 1) (hb : d152855 q = 1) : d156993 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12821, d156993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30187 q ha hb
    | true =>
      simp only [d12821, d156993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d12822 q = 1) (hb : d152855 q = 1) : d156994 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12822, d156994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d12822, d156994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d115361 q = 1) (hb : d152855 q = 1) : d156995 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115361, d156995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d115361, d156995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d115362 q = 1) (hb : d152855 q = 1) : d156996 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115362, d156996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d115362, d156996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d115363 q = 1) (hb : d152855 q = 1) : d156997 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115363, d156997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d115363, d156997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d115364 q = 1) (hb : d152855 q = 1) : d156998 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115364, d156998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d115364, d156998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro30189 (p : Pattern) (ha : d115371 p = 1) (hb : d152855 p = 1) : d157018 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12815 q = 1) (hb : d152855 q = 1) : d156990 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12815, d156990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30186 q ha hb
    | true =>
      simp only [d12815, d156990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30159 q ha hb
  have h2 (q : Pattern) (ha : d115360 q = 1) (hb : d152855 q = 1) : d156991 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115360, d156991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115360, d156991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d12821 q = 1) (hb : d152855 q = 1) : d156993 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12821, d156993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30187 q ha hb
    | true =>
      simp only [d12821, d156993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12822 q = 1) (hb : d152855 q = 1) : d156994 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12822, d156994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12822, d156994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d115361 q = 1) (hb : d152855 q = 1) : d156995 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115361, d156995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115361, d156995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115369 q = 1) (hb : d152855 q = 1) : d157016 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115369, d157016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115369, d157016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d115370 q = 1) (hb : d152855 q = 1) : d157017 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115370, d157017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115370, d157017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d115371 q = 1) (hb : d152855 q = 1) : d157018 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115371, d157018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115371, d157018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro30190 (p : Pattern) (ha : d12854 p = 1) (hb : d152855 p = 1) : d157031 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d965 q = 1) (hb : d152854 q = 1) : d157026 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d965, d157026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d965, d157026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30174 q ha hb
  have h2 (q : Pattern) (ha : d834 q = 1) (hb : d152854 q = 1) : d156936 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d834, d156936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30174 q ha hb
    | true =>
      simp only [d834, d156936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d966 q = 1) (hb : d152854 q = 1) : d157027 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d966, d157027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d966, d157027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d835 q = 1) (hb : d152854 q = 1) : d156937 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d835, d156937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d835, d156937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d967 q = 1) (hb : d152854 q = 1) : d157028 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d967, d157028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d967, d157028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d968 q = 1) (hb : d152854 q = 1) : d157029 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d968, d157029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d968, d157029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d659 q = 1) (hb : d152854 q = 1) : d156824 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d659, d156824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d659, d156824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30125 q ha hb
  have h8 (q : Pattern) (ha : d543 q = 1) (hb : d152854 q = 1) : d156759 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d543, d156759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30125 q ha hb
    | true =>
      simp only [d543, d156759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d660 q = 1) (hb : d152854 q = 1) : d156825 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d660, d156825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d660, d156825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d544 q = 1) (hb : d152854 q = 1) : d156760 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d544, d156760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d544, d156760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d661 q = 1) (hb : d152854 q = 1) : d156826 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d661, d156826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d661, d156826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d662 q = 1) (hb : d152854 q = 1) : d156827 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d662, d156827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d662, d156827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d969 q = 1) (hb : d152854 q = 1) : d157030 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d969, d157030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d969, d157030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d12854 q = 1) (hb : d152855 q = 1) : d157031 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d12854, d152855, d157031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d12854, d152855, d157031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro30191 (p : Pattern) (ha : d12863 p = 1) (hb : d152855 p = 1) : d157040 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12858 q = 1) (hb : d152854 q = 1) : d157035 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d12858, d157035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12858, d157035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30176 q ha hb
  have h2 (q : Pattern) (ha : d9468 q = 1) (hb : d152854 q = 1) : d156948 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9468, d156948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30176 q ha hb
    | true =>
      simp only [d9468, d156948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d12859 q = 1) (hb : d152854 q = 1) : d157036 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d12859, d157036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d12859, d157036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d9470 q = 1) (hb : d152854 q = 1) : d156949 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9470, d156949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9470, d156949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12860 q = 1) (hb : d152854 q = 1) : d157037 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d12860, d157037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12860, d157037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12861 q = 1) (hb : d152854 q = 1) : d157038 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d12861, d157038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12861, d157038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d971 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30151 q ha hb
  have h8 (q : Pattern) (ha : d751 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30151 q ha hb
    | true =>
      simp only [d751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d972 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d752 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d973 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d974 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d12862 q = 1) (hb : d152854 q = 1) : d157039 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d12862, d157039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12862, d157039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d12863 q = 1) (hb : d152855 q = 1) : d157040 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d12863, d152855, d157040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d12863, d152855, d157040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro30192 (p : Pattern) (ha : d12873 p = 1) (hb : d152855 p = 1) : d157055 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12855 q = 1) (hb : d152855 q = 1) : d157032 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12855, d157032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30190 q ha hb
    | true =>
      simp only [d12855, d157032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30141 q ha hb
  have h2 (q : Pattern) (ha : d12856 q = 1) (hb : d152855 q = 1) : d157033 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12856, d157033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12856, d157033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12857 q = 1) (hb : d152855 q = 1) : d157034 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12857, d157034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12857, d157034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d12864 q = 1) (hb : d152855 q = 1) : d157041 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12864, d157041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30141 q ha hb
    | true =>
      simp only [d12864, d157041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30191 q ha hb
  have h5 (q : Pattern) (ha : d12865 q = 1) (hb : d152855 q = 1) : d157042 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12865, d157042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12865, d157042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12866 q = 1) (hb : d152855 q = 1) : d157043 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12866, d157043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12866, d157043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12867 q = 1) (hb : d152855 q = 1) : d157044 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12867, d157044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12867, d157044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12868 q = 1) (hb : d152855 q = 1) : d157047 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12868, d157047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30141 q ha hb
    | true =>
      simp only [d12868, d157047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30166 q ha hb
  have h9 (q : Pattern) (ha : d12869 q = 1) (hb : d152855 q = 1) : d157048 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12869, d157048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12869, d157048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d12870 q = 1) (hb : d152855 q = 1) : d157049 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12870, d157049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12870, d157049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d6211 q = 1) (hb : d152855 q = 1) : d157050 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d6211, d157050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30166 q ha hb
    | true =>
      simp only [d6211, d157050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30165 q ha hb
  have h12 (q : Pattern) (ha : d6212 q = 1) (hb : d152855 q = 1) : d157051 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d6212, d157051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6212, d157051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d6213 q = 1) (hb : d152855 q = 1) : d157052 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d6213, d157052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6213, d157052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d12871 q = 1) (hb : d152855 q = 1) : d157053 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12871, d157053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d12871, d157053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d12872 q = 1) (hb : d152855 q = 1) : d157054 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12872, d157054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12872, d157054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d12873 q = 1) (hb : d152855 q = 1) : d157055 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12873, d157055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d12873, d157055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro30193 (p : Pattern) (ha : d12877 p = 1) (hb : d152855 p = 1) : d157060 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12868 q = 1) (hb : d152855 q = 1) : d157047 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12868, d157047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30141 q ha hb
    | true =>
      simp only [d12868, d157047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30166 q ha hb
  have h2 (q : Pattern) (ha : d12869 q = 1) (hb : d152855 q = 1) : d157048 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12869, d157048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12869, d157048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12870 q = 1) (hb : d152855 q = 1) : d157049 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12870, d157049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12870, d157049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d6211 q = 1) (hb : d152855 q = 1) : d157050 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d6211, d157050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30166 q ha hb
    | true =>
      simp only [d6211, d157050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30165 q ha hb
  have h5 (q : Pattern) (ha : d6212 q = 1) (hb : d152855 q = 1) : d157051 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d6212, d157051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6212, d157051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6213 q = 1) (hb : d152855 q = 1) : d157052 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d6213, d157052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6213, d157052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12871 q = 1) (hb : d152855 q = 1) : d157053 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12871, d157053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12871, d157053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d6214 q = 1) (hb : d152855 q = 1) : d157058 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d6214, d157058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6214, d157058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d12876 q = 1) (hb : d152855 q = 1) : d157059 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12876, d157059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12876, d157059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d12877 q = 1) (hb : d152855 q = 1) : d157060 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12877, d157060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d12877, d157060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro30194 (p : Pattern) (ha : d12883 p = 1) (hb : d152855 p = 1) : d157066 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12874 q = 1) (hb : d152855 q = 1) : d157056 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12874, d157056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30192 q ha hb
    | true =>
      simp only [d12874, d157056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12875 q = 1) (hb : d152855 q = 1) : d157057 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12875, d157057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12875, d157057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12878 q = 1) (hb : d152855 q = 1) : d157061 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12878, d157061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30193 q ha hb
    | true =>
      simp only [d12878, d157061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12879 q = 1) (hb : d152855 q = 1) : d157062 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12879, d157062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12879, d157062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12880 q = 1) (hb : d152855 q = 1) : d157063 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12880, d157063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12880, d157063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12881 q = 1) (hb : d152855 q = 1) : d157064 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12881, d157064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12881, d157064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12882 q = 1) (hb : d152855 q = 1) : d157065 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12882, d157065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12882, d157065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12883 q = 1) (hb : d152855 q = 1) : d157066 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12883, d157066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12883, d157066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro30195 (p : Pattern) (ha : d12891 p = 1) (hb : d152855 p = 1) : d157074 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12878 q = 1) (hb : d152855 q = 1) : d157061 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12878, d157061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30193 q ha hb
    | true =>
      simp only [d12878, d157061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12879 q = 1) (hb : d152855 q = 1) : d157062 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12879, d157062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12879, d157062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12886 q = 1) (hb : d152855 q = 1) : d157069 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12886, d157069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30167 q ha hb
    | true =>
      simp only [d12886, d157069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12887 q = 1) (hb : d152855 q = 1) : d157070 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12887, d157070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12887, d157070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12888 q = 1) (hb : d152855 q = 1) : d157071 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12888, d157071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12888, d157071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12889 q = 1) (hb : d152855 q = 1) : d157072 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12889, d157072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12889, d157072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12890 q = 1) (hb : d152855 q = 1) : d157073 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12890, d157073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12890, d157073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12891 q = 1) (hb : d152855 q = 1) : d157074 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12891, d157074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12891, d157074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro30196 (p : Pattern) (ha : d12924 p = 1) (hb : d152855 p = 1) : d157080 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12878 q = 1) (hb : d152855 q = 1) : d157061 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12878, d157061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30193 q ha hb
    | true =>
      simp only [d12878, d157061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12879 q = 1) (hb : d152855 q = 1) : d157062 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12879, d157062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12879, d157062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12921 q = 1) (hb : d152855 q = 1) : d157077 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12921, d157077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12921, d157077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12922 q = 1) (hb : d152855 q = 1) : d157078 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12922, d157078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12922, d157078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12923 q = 1) (hb : d152855 q = 1) : d157079 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12923, d157079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12923, d157079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12924 q = 1) (hb : d152855 q = 1) : d157080 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12924, d157080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12924, d157080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro30197 (p : Pattern) (ha : d115381 p = 1) (hb : d152855 p = 1) : d157086 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12892 q = 1) (hb : d152855 q = 1) : d157075 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12892, d157075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30194 q ha hb
    | true =>
      simp only [d12892, d157075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30195 q ha hb
  have h2 (q : Pattern) (ha : d115377 q = 1) (hb : d152855 q = 1) : d157076 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115377, d157076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115377, d157076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d12925 q = 1) (hb : d152855 q = 1) : d157081 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12925, d157081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30196 q ha hb
    | true =>
      simp only [d12925, d157081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12926 q = 1) (hb : d152855 q = 1) : d157082 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12926, d157082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12926, d157082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d115378 q = 1) (hb : d152855 q = 1) : d157083 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115378, d157083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115378, d157083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115379 q = 1) (hb : d152855 q = 1) : d157084 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115379, d157084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115379, d157084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d115380 q = 1) (hb : d152855 q = 1) : d157085 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115380, d157085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115380, d157085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d115381 q = 1) (hb : d152855 q = 1) : d157086 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115381, d157086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115381, d157086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro30198 (p : Pattern) (ha : d115387 p = 1) (hb : d152855 p = 1) : d157103 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12714 q = 1) (hb : d152855 q = 1) : d156905 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12714, d156905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12714, d156905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30158 q ha hb
  have h2 (q : Pattern) (ha : d12715 q = 1) (hb : d152855 q = 1) : d156906 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d12715, d156906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d12715, d156906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d12724 q = 1) (hb : d152855 q = 1) : d156915 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12724, d156915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30158 q ha hb
    | true =>
      simp only [d12724, d156915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30161 q ha hb
  have h4 (q : Pattern) (ha : d12725 q = 1) (hb : d152855 q = 1) : d156916 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d12725, d156916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12725, d156916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12726 q = 1) (hb : d152855 q = 1) : d156917 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d12726, d156917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12726, d156917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115365 q = 1) (hb : d152855 q = 1) : d156999 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115365, d156999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30181 q ha hb
    | true =>
      simp only [d115365, d156999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30188 q ha hb
  have h7 (q : Pattern) (ha : d12840 q = 1) (hb : d152855 q = 1) : d157012 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12840, d157012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30162 q ha hb
    | true =>
      simp only [d12840, d157012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30163 q ha hb
  have h8 (q : Pattern) (ha : d115366 q = 1) (hb : d152855 q = 1) : d157013 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115366, d157013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d115366, d157013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d115367 q = 1) (hb : d152855 q = 1) : d157014 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115367, d157014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d115367, d157014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d115368 q = 1) (hb : d152855 q = 1) : d157015 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115368, d157015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d115368, d157015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d115372 q = 1) (hb : d152855 q = 1) : d157019 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115372, d157019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115372, d157019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30189 q ha hb
  have h12 (q : Pattern) (ha : d12849 q = 1) (hb : d152855 q = 1) : d157021 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12849, d157021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12849, d157021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30164 q ha hb
  have h13 (q : Pattern) (ha : d115373 q = 1) (hb : d152855 q = 1) : d157022 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115373, d157022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d115373, d157022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d115374 q = 1) (hb : d152855 q = 1) : d157023 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115374, d157023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d115374, d157023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d115375 q = 1) (hb : d152855 q = 1) : d157024 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115375, d157024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d115375, d157024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d115376 q = 1) (hb : d152855 q = 1) : d157025 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d115376, d157025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d115376, d157025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d115382 q = 1) (hb : d152855 q = 1) : d157087 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115382, d157087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115382, d157087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30197 q ha hb
  have h18 (q : Pattern) (ha : d12942 q = 1) (hb : d152855 q = 1) : d157098 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12942, d157098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12942, d157098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30169 q ha hb
  have h19 (q : Pattern) (ha : d115383 q = 1) (hb : d152855 q = 1) : d157099 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115383, d157099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d115383, d157099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d115384 q = 1) (hb : d152855 q = 1) : d157100 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115384, d157100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d115384, d157100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d115385 q = 1) (hb : d152855 q = 1) : d157101 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115385, d157101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d115385, d157101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d115386 q = 1) (hb : d152855 q = 1) : d157102 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d115386, d157102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d115386, d157102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d115387 q = 1) (hb : d152855 q = 1) : d157103 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d115387, d157103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d115387, d157103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro30199 (p : Pattern) (ha : d115393 p = 1) (hb : d152855 p = 1) : d157109 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d115388 q = 1) (hb : d152855 q = 1) : d157104 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d115388, d157104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115388, d157104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30198 q ha hb
  have h2 (q : Pattern) (ha : d115389 q = 1) (hb : d152855 q = 1) : d157105 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d115389, d157105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115389, d157105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d115390 q = 1) (hb : d152855 q = 1) : d157106 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d115390, d157106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115390, d157106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d115391 q = 1) (hb : d152855 q = 1) : d157107 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d115391, d157107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115391, d157107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d115392 q = 1) (hb : d152855 q = 1) : d157108 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d115392, d157108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115392, d157108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115393 q = 1) (hb : d152855 q = 1) : d157109 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d115393, d157109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115393, d157109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro30200 (p : Pattern) (ha : d1109 p = 1) (hb : d152854 p = 1) : d157117 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1098 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d1095 q = 1) : d1095 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1105 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1106 q = 1) (hb : d152852 q = 1) : d26089 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1106, d152852, d26089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d1106, d152852, d26089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d1 q = 1) (hb : d134 q = 1) : d134 q = 1 := by
    exact hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d20 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d135 q = 1) (hb : d152852 q = 1) : d9796 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d135, d152852, d9796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d135, d152852, d9796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d1107 q = 1) (hb : d152852 q = 1) : d26105 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d1107, d26105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1107, d26105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d152852 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d1108 q = 1) (hb : d152852 q = 1) : d26106 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d1108, d26106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1108, d26106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1109 q = 1) (hb : d152854 q = 1) : d157117 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d1109, d152854, d157117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1109, d152854, d157117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro30201 (p : Pattern) (ha : d1120 p = 1) (hb : d152854 p = 1) : d157124 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1108 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d1116 q = 1) : d1116 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d20 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1117 q = 1) (hb : d152852 q = 1) : d1132 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1117, d152852, d1132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d1117, d152852, d1132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d21 q = 1) (hb : d152852 q = 1) : d21 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d1118 q = 1) (hb : d152852 q = 1) : d9841 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d1118, d9841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1118, d9841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d152852 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d1119 q = 1) (hb : d152852 q = 1) : d9842 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d1119, d9842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1119, d9842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1120 q = 1) (hb : d152854 q = 1) : d157124 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d1120, d152854, d157124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1120, d152854, d157124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro30202 (p : Pattern) (ha : d5009 p = 1) (hb : d152855 p = 1) : d157130 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1110 q = 1) (hb : d152854 q = 1) : d157118 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1110, d157118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30200 q ha hb
    | true =>
      simp only [d1110, d157118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1111 q = 1) (hb : d152854 q = 1) : d157119 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1111, d157119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1111, d157119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1112 q = 1) (hb : d152854 q = 1) : d157120 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1112, d157120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1112, d157120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1113 q = 1) (hb : d152854 q = 1) : d157121 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1113, d157121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1113, d157121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1121 q = 1) (hb : d152854 q = 1) : d157125 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1121, d157125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30201 q ha hb
    | true =>
      simp only [d1121, d157125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1122 q = 1) (hb : d152854 q = 1) : d157126 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1122, d157126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1122, d157126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1123 q = 1) (hb : d152854 q = 1) : d157127 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1123, d157127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1123, d157127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1124 q = 1) (hb : d152854 q = 1) : d157128 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1124, d157128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1124, d157128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d1125 q = 1) (hb : d152854 q = 1) : d157129 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1125, d157129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1125, d157129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d5009 q = 1) (hb : d152855 q = 1) : d157130 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d5009, d152855, d157130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d5009, d152855, d157130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro30203 (p : Pattern) (ha : d5017 p = 1) (hb : d152854 p = 1) : d157124 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d5016 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d1116 q = 1) : d1116 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d20 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1117 q = 1) (hb : d152852 q = 1) : d1132 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1117, d152852, d1132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d1117, d152852, d1132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d21 q = 1) (hb : d152852 q = 1) : d21 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d1118 q = 1) (hb : d152852 q = 1) : d9841 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d1118, d9841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1118, d9841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d152852 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d1119 q = 1) (hb : d152852 q = 1) : d9842 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d1119, d9842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1119, d9842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d5017 q = 1) (hb : d152854 q = 1) : d157124 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d5017, d152854, d157124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d5017, d152854, d157124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro30204 (p : Pattern) (ha : d5023 p = 1) (hb : d152855 p = 1) : d157135 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5018 q = 1) (hb : d152854 q = 1) : d157125 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5018, d157125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30203 q ha hb
    | true =>
      simp only [d5018, d157125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d5019 q = 1) (hb : d152854 q = 1) : d157126 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5019, d157126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5019, d157126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d5020 q = 1) (hb : d152854 q = 1) : d157127 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d5020, d157127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5020, d157127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d5021 q = 1) (hb : d152854 q = 1) : d157128 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d5021, d157128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5021, d157128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5022 q = 1) (hb : d152854 q = 1) : d157134 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d5022, d157134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5022, d157134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d5023 q = 1) (hb : d152855 q = 1) : d157135 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d5023, d152855, d157135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5023, d152855, d157135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro30205 (p : Pattern) (ha : d1099 p = 1) (hb : d152854 p = 1) : d157112 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d1089 q = 1) : d1089 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1095 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1096 q = 1) (hb : d152852 q = 1) : d26079 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1096, d152852, d26079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d1096, d152852, d26079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d1 q = 1) (hb : d538 q = 1) : d538 q = 1 := by
    exact hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d134 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d539 q = 1) (hb : d152852 q = 1) : d25429 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d539, d152852, d25429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d539, d152852, d25429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d1097 q = 1) (hb : d152852 q = 1) : d26087 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d1097, d26087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1097, d26087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d152852 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d1098 q = 1) (hb : d152852 q = 1) : d26088 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d1098, d26088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1098, d26088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1099 q = 1) (hb : d152854 q = 1) : d157112 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d1099, d152854, d157112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1099, d152854, d157112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro30206 (p : Pattern) (ha : d12956 p = 1) (hb : d152855 p = 1) : d157123 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1100 q = 1) (hb : d152854 q = 1) : d157113 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1100, d157113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30205 q ha hb
    | true =>
      simp only [d1100, d157113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1101 q = 1) (hb : d152854 q = 1) : d157114 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1101, d157114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1101, d157114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1102 q = 1) (hb : d152854 q = 1) : d157115 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1102, d157115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1102, d157115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1103 q = 1) (hb : d152854 q = 1) : d157116 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1103, d157116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1103, d157116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1110 q = 1) (hb : d152854 q = 1) : d157118 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1110, d157118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30200 q ha hb
    | true =>
      simp only [d1110, d157118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1111 q = 1) (hb : d152854 q = 1) : d157119 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1111, d157119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1111, d157119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1112 q = 1) (hb : d152854 q = 1) : d157120 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1112, d157120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1112, d157120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1113 q = 1) (hb : d152854 q = 1) : d157121 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1113, d157121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1113, d157121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d1114 q = 1) (hb : d152854 q = 1) : d157122 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1114, d157122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1114, d157122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d12956 q = 1) (hb : d152855 q = 1) : d157123 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d12956, d152855, d157123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d12956, d152855, d157123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro30207 (p : Pattern) (ha : d12961 p = 1) (hb : d152855 p = 1) : d157135 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1121 q = 1) (hb : d152854 q = 1) : d157125 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1121, d157125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30201 q ha hb
    | true =>
      simp only [d1121, d157125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1122 q = 1) (hb : d152854 q = 1) : d157126 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1122, d157126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1122, d157126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1123 q = 1) (hb : d152854 q = 1) : d157127 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1123, d157127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1123, d157127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1124 q = 1) (hb : d152854 q = 1) : d157128 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1124, d157128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1124, d157128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1127 q = 1) (hb : d152854 q = 1) : d157134 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1127, d157134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1127, d157134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d12961 q = 1) (hb : d152855 q = 1) : d157135 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d12961, d152855, d157135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12961, d152855, d157135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro30208 (p : Pattern) (ha : d12967 p = 1) (hb : d152855 p = 1) : d157142 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12957 q = 1) (hb : d152855 q = 1) : d157131 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12957, d157131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30206 q ha hb
    | true =>
      simp only [d12957, d157131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30202 q ha hb
  have h2 (q : Pattern) (ha : d12958 q = 1) (hb : d152855 q = 1) : d157132 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12958, d157132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12958, d157132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12959 q = 1) (hb : d152855 q = 1) : d157133 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12959, d157133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12959, d157133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d5024 q = 1) (hb : d152855 q = 1) : d157136 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d5024, d157136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30202 q ha hb
    | true =>
      simp only [d5024, d157136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30204 q ha hb
  have h5 (q : Pattern) (ha : d5025 q = 1) (hb : d152855 q = 1) : d157137 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d5025, d157137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5025, d157137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d5026 q = 1) (hb : d152855 q = 1) : d157138 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d5026, d157138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5026, d157138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12960 q = 1) (hb : d152855 q = 1) : d157139 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12960, d157139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12960, d157139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12962 q = 1) (hb : d152855 q = 1) : d157136 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12962, d157136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30202 q ha hb
    | true =>
      simp only [d12962, d157136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30207 q ha hb
  have h9 (q : Pattern) (ha : d12963 q = 1) (hb : d152855 q = 1) : d157137 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12963, d157137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12963, d157137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d12964 q = 1) (hb : d152855 q = 1) : d157138 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12964, d157138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12964, d157138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d12965 q = 1) (hb : d152855 q = 1) : d157140 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12965, d157140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d12965, d157140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d12966 q = 1) (hb : d152855 q = 1) : d157141 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12966, d157141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12966, d157141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d12967 q = 1) (hb : d152855 q = 1) : d157142 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12967, d157142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d12967, d157142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro30209 (p : Pattern) (ha : d12971 p = 1) (hb : d152855 p = 1) : d157146 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12962 q = 1) (hb : d152855 q = 1) : d157136 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12962, d157136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30202 q ha hb
    | true =>
      simp only [d12962, d157136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30207 q ha hb
  have h2 (q : Pattern) (ha : d12963 q = 1) (hb : d152855 q = 1) : d157137 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12963, d157137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12963, d157137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12964 q = 1) (hb : d152855 q = 1) : d157138 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12964, d157138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12964, d157138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d12965 q = 1) (hb : d152855 q = 1) : d157140 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12965, d157140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12965, d157140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12970 q = 1) (hb : d152855 q = 1) : d157145 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12970, d157145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12970, d157145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12971 q = 1) (hb : d152855 q = 1) : d157146 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12971, d157146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12971, d157146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro30210 (p : Pattern) (ha : d12977 p = 1) (hb : d152855 p = 1) : d157152 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12968 q = 1) (hb : d152855 q = 1) : d157143 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12968, d157143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30208 q ha hb
    | true =>
      simp only [d12968, d157143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12969 q = 1) (hb : d152855 q = 1) : d157144 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12969, d157144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12969, d157144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12972 q = 1) (hb : d152855 q = 1) : d157147 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12972, d157147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30209 q ha hb
    | true =>
      simp only [d12972, d157147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12973 q = 1) (hb : d152855 q = 1) : d157148 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12973, d157148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12973, d157148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12974 q = 1) (hb : d152855 q = 1) : d157149 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12974, d157149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12974, d157149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12975 q = 1) (hb : d152855 q = 1) : d157150 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12975, d157150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12975, d157150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12976 q = 1) (hb : d152855 q = 1) : d157151 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12976, d157151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12976, d157151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12977 q = 1) (hb : d152855 q = 1) : d157152 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12977, d157152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12977, d157152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro30211 (p : Pattern) (ha : d12981 p = 1) (hb : d152855 p = 1) : d157156 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12972 q = 1) (hb : d152855 q = 1) : d157147 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12972, d157147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30209 q ha hb
    | true =>
      simp only [d12972, d157147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12973 q = 1) (hb : d152855 q = 1) : d157148 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12973, d157148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12973, d157148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12978 q = 1) (hb : d152855 q = 1) : d157153 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12978, d157153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12978, d157153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12979 q = 1) (hb : d152855 q = 1) : d157154 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12979, d157154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12979, d157154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12980 q = 1) (hb : d152855 q = 1) : d157155 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12980, d157155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12980, d157155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12981 q = 1) (hb : d152855 q = 1) : d157156 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12981, d157156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12981, d157156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro30212 (p : Pattern) (ha : d12987 p = 1) (hb : d152855 p = 1) : d157162 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12982 q = 1) (hb : d152855 q = 1) : d157157 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12982, d157157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30210 q ha hb
    | true =>
      simp only [d12982, d157157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30211 q ha hb
  have h2 (q : Pattern) (ha : d12983 q = 1) (hb : d152855 q = 1) : d157158 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12983, d157158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12983, d157158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12984 q = 1) (hb : d152855 q = 1) : d157159 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12984, d157159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12984, d157159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12985 q = 1) (hb : d152855 q = 1) : d157160 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12985, d157160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12985, d157160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12986 q = 1) (hb : d152855 q = 1) : d157161 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12986, d157161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12986, d157161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12987 q = 1) (hb : d152855 q = 1) : d157162 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d12987, d157162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12987, d157162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro30213 (p : Pattern) (ha : d12990 p = 1) (hb : d152855 p = 1) : d157165 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12968 q = 1) (hb : d152855 q = 1) : d157143 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12968, d157143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30208 q ha hb
    | true =>
      simp only [d12968, d157143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12969 q = 1) (hb : d152855 q = 1) : d157144 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12969, d157144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12969, d157144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12972 q = 1) (hb : d152855 q = 1) : d157147 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12972, d157147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30209 q ha hb
    | true =>
      simp only [d12972, d157147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12973 q = 1) (hb : d152855 q = 1) : d157148 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12973, d157148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12973, d157148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12974 q = 1) (hb : d152855 q = 1) : d157149 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12974, d157149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12974, d157149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12975 q = 1) (hb : d152855 q = 1) : d157150 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12975, d157150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12975, d157150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12976 q = 1) (hb : d152855 q = 1) : d157151 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12976, d157151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12976, d157151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12990 q = 1) (hb : d152855 q = 1) : d157165 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12990, d157165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12990, d157165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro30214 (p : Pattern) (ha : d12991 p = 1) (hb : d152855 p = 1) : d157166 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12972 q = 1) (hb : d152855 q = 1) : d157147 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12972, d157147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30209 q ha hb
    | true =>
      simp only [d12972, d157147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12973 q = 1) (hb : d152855 q = 1) : d157148 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12973, d157148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12973, d157148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12978 q = 1) (hb : d152855 q = 1) : d157153 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12978, d157153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12978, d157153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12979 q = 1) (hb : d152855 q = 1) : d157154 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12979, d157154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12979, d157154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12980 q = 1) (hb : d152855 q = 1) : d157155 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12980, d157155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12980, d157155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12991 q = 1) (hb : d152855 q = 1) : d157166 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12991, d157166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12991, d157166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro30215 (p : Pattern) (ha : d12997 p = 1) (hb : d152855 p = 1) : d157172 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12982 q = 1) (hb : d152855 q = 1) : d157157 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12982, d157157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30210 q ha hb
    | true =>
      simp only [d12982, d157157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30211 q ha hb
  have h2 (q : Pattern) (ha : d12983 q = 1) (hb : d152855 q = 1) : d157158 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12983, d157158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12983, d157158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12984 q = 1) (hb : d152855 q = 1) : d157159 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12984, d157159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12984, d157159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12985 q = 1) (hb : d152855 q = 1) : d157160 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12985, d157160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12985, d157160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12986 q = 1) (hb : d152855 q = 1) : d157161 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12986, d157161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12986, d157161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12992 q = 1) (hb : d152855 q = 1) : d157167 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12992, d157167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30213 q ha hb
    | true =>
      simp only [d12992, d157167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30214 q ha hb
  have h7 (q : Pattern) (ha : d12993 q = 1) (hb : d152855 q = 1) : d157168 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12993, d157168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12993, d157168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12994 q = 1) (hb : d152855 q = 1) : d157169 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12994, d157169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12994, d157169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d12995 q = 1) (hb : d152855 q = 1) : d157170 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12995, d157170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12995, d157170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d12996 q = 1) (hb : d152855 q = 1) : d157171 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12996, d157171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12996, d157171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d12997 q = 1) (hb : d152855 q = 1) : d157172 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d12997, d157172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12997, d157172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro30216 (p : Pattern) (ha : d13040 p = 1) (hb : d152855 p = 1) : d157142 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12957 q = 1) (hb : d152855 q = 1) : d157131 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12957, d157131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30206 q ha hb
    | true =>
      simp only [d12957, d157131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30202 q ha hb
  have h2 (q : Pattern) (ha : d12958 q = 1) (hb : d152855 q = 1) : d157132 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12958, d157132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12958, d157132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12959 q = 1) (hb : d152855 q = 1) : d157133 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12959, d157133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12959, d157133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d5024 q = 1) (hb : d152855 q = 1) : d157136 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d5024, d157136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30202 q ha hb
    | true =>
      simp only [d5024, d157136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30204 q ha hb
  have h5 (q : Pattern) (ha : d5025 q = 1) (hb : d152855 q = 1) : d157137 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d5025, d157137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5025, d157137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d5026 q = 1) (hb : d152855 q = 1) : d157138 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d5026, d157138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5026, d157138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12960 q = 1) (hb : d152855 q = 1) : d157139 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12960, d157139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12960, d157139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d5027 q = 1) (hb : d152855 q = 1) : d157140 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d5027, d157140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d5027, d157140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d13039 q = 1) (hb : d152855 q = 1) : d157141 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13039, d157141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13039, d157141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d13040 q = 1) (hb : d152855 q = 1) : d157142 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13040, d157142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d13040, d157142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro30217 (p : Pattern) (ha : d13050 p = 1) (hb : d152855 p = 1) : d157152 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13041 q = 1) (hb : d152855 q = 1) : d157143 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13041, d157143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30216 q ha hb
    | true =>
      simp only [d13041, d157143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13042 q = 1) (hb : d152855 q = 1) : d157144 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13042, d157144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13042, d157144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12972 q = 1) (hb : d152855 q = 1) : d157147 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12972, d157147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30209 q ha hb
    | true =>
      simp only [d12972, d157147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12973 q = 1) (hb : d152855 q = 1) : d157148 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12973, d157148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12973, d157148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13047 q = 1) (hb : d152855 q = 1) : d157149 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13047, d157149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13047, d157149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13048 q = 1) (hb : d152855 q = 1) : d157150 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13048, d157150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13048, d157150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13049 q = 1) (hb : d152855 q = 1) : d157151 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13049, d157151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13049, d157151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13050 q = 1) (hb : d152855 q = 1) : d157152 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13050, d157152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13050, d157152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro30218 (p : Pattern) (ha : d13134 p = 1) (hb : d152855 p = 1) : d157264 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13124 q = 1) (hb : d152855 q = 1) : d157157 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13124, d157157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30217 q ha hb
    | true =>
      simp only [d13124, d157157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30211 q ha hb
  have h2 (q : Pattern) (ha : d13125 q = 1) (hb : d152855 q = 1) : d157158 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13125, d157158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13125, d157158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13126 q = 1) (hb : d152855 q = 1) : d157159 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13126, d157159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13126, d157159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13127 q = 1) (hb : d152855 q = 1) : d157160 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13127, d157160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13127, d157160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13128 q = 1) (hb : d152855 q = 1) : d157161 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13128, d157161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13128, d157161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13129 q = 1) (hb : d152855 q = 1) : d157259 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13129, d157259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30211 q ha hb
    | true =>
      simp only [d13129, d157259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13130 q = 1) (hb : d152855 q = 1) : d157260 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13130, d157260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13130, d157260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d13131 q = 1) (hb : d152855 q = 1) : d157261 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13131, d157261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13131, d157261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d13132 q = 1) (hb : d152855 q = 1) : d157262 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13132, d157262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13132, d157262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d13133 q = 1) (hb : d152855 q = 1) : d157263 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13133, d157263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13133, d157263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d13134 q = 1) (hb : d152855 q = 1) : d157264 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d13134, d157264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13134, d157264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro30219 (p : Pattern) (ha : d13140 p = 1) (hb : d152855 p = 1) : d157270 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13129 q = 1) (hb : d152855 q = 1) : d157259 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13129, d157259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30211 q ha hb
    | true =>
      simp only [d13129, d157259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13130 q = 1) (hb : d152855 q = 1) : d157260 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13130, d157260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13130, d157260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13131 q = 1) (hb : d152855 q = 1) : d157261 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13131, d157261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13131, d157261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13132 q = 1) (hb : d152855 q = 1) : d157262 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13132, d157262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13132, d157262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13133 q = 1) (hb : d152855 q = 1) : d157263 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13133, d157263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13133, d157263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13135 q = 1) (hb : d152855 q = 1) : d157265 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13135, d157265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30214 q ha hb
    | true =>
      simp only [d13135, d157265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13136 q = 1) (hb : d152855 q = 1) : d157266 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13136, d157266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13136, d157266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d13137 q = 1) (hb : d152855 q = 1) : d157267 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13137, d157267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13137, d157267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d13138 q = 1) (hb : d152855 q = 1) : d157268 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13138, d157268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13138, d157268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d13139 q = 1) (hb : d152855 q = 1) : d157269 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13139, d157269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13139, d157269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d13140 q = 1) (hb : d152855 q = 1) : d157270 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d13140, d157270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13140, d157270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro30220 (p : Pattern) (ha : d13149 p = 1) (hb : d152855 p = 1) : d157279 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13135 q = 1) (hb : d152855 q = 1) : d157265 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13135, d157265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30214 q ha hb
    | true =>
      simp only [d13135, d157265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13136 q = 1) (hb : d152855 q = 1) : d157266 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13136, d157266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13136, d157266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13137 q = 1) (hb : d152855 q = 1) : d157267 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13137, d157267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13137, d157267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13138 q = 1) (hb : d152855 q = 1) : d157268 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13138, d157268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13138, d157268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13139 q = 1) (hb : d152855 q = 1) : d157269 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13139, d157269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13139, d157269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13149 q = 1) (hb : d152855 q = 1) : d157279 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d13149, d157279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13149, d157279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro30221 (p : Pattern) (ha : d6349 p = 1) (hb : d152855 p = 1) : d157319 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1385 q = 1) (hb : d152854 q = 1) : d157295 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1385, d157295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1385, d157295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30200 q ha hb
  have h2 (q : Pattern) (ha : d1110 q = 1) (hb : d152854 q = 1) : d157118 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1110, d157118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30200 q ha hb
    | true =>
      simp only [d1110, d157118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1386 q = 1) (hb : d152854 q = 1) : d157296 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1386, d157296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1386, d157296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1111 q = 1) (hb : d152854 q = 1) : d157119 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1111, d157119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1111, d157119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1387 q = 1) (hb : d152854 q = 1) : d157297 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1387, d157297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1387, d157297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1388 q = 1) (hb : d152854 q = 1) : d157298 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1388, d157298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1388, d157298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1391 q = 1) (hb : d152854 q = 1) : d157314 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1391, d157314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1391, d157314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30201 q ha hb
  have h8 (q : Pattern) (ha : d1121 q = 1) (hb : d152854 q = 1) : d157125 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1121, d157125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30201 q ha hb
    | true =>
      simp only [d1121, d157125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d1392 q = 1) (hb : d152854 q = 1) : d157315 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1392, d157315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1392, d157315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1122 q = 1) (hb : d152854 q = 1) : d157126 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1122, d157126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1122, d157126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d1393 q = 1) (hb : d152854 q = 1) : d157316 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1393, d157316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d1393, d157316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d1394 q = 1) (hb : d152854 q = 1) : d157317 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1394, d157317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d1394, d157317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d1395 q = 1) (hb : d152854 q = 1) : d157318 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1395, d157318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1395, d157318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d6349 q = 1) (hb : d152855 q = 1) : d157319 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d6349, d152855, d157319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d6349, d152855, d157319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro30222 (p : Pattern) (ha : d13190 p = 1) (hb : d152855 p = 1) : d157324 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1391 q = 1) (hb : d152854 q = 1) : d157314 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1391, d157314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1391, d157314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30201 q ha hb
  have h2 (q : Pattern) (ha : d1121 q = 1) (hb : d152854 q = 1) : d157125 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1121, d157125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30201 q ha hb
    | true =>
      simp only [d1121, d157125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1392 q = 1) (hb : d152854 q = 1) : d157315 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1392, d157315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1392, d157315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1122 q = 1) (hb : d152854 q = 1) : d157126 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1122, d157126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1122, d157126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1393 q = 1) (hb : d152854 q = 1) : d157316 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1393, d157316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1393, d157316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1394 q = 1) (hb : d152854 q = 1) : d157317 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1394, d157317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1394, d157317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1400 q = 1) (hb : d152854 q = 1) : d157323 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1400, d157323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1400, d157323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d13190 q = 1) (hb : d152855 q = 1) : d157324 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13190, d152855, d157324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13190, d152855, d157324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro30223 (p : Pattern) (ha : d13196 p = 1) (hb : d152855 p = 1) : d157343 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13191 q = 1) (hb : d152855 q = 1) : d157325 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13191, d157325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30221 q ha hb
    | true =>
      simp only [d13191, d157325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30222 q ha hb
  have h2 (q : Pattern) (ha : d13192 q = 1) (hb : d152855 q = 1) : d157326 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13192, d157326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13192, d157326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13193 q = 1) (hb : d152855 q = 1) : d157327 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13193, d157327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13193, d157327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d13194 q = 1) (hb : d152855 q = 1) : d157333 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13194, d157333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13194, d157333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13195 q = 1) (hb : d152855 q = 1) : d157342 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13195, d157342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13195, d157342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13196 q = 1) (hb : d152855 q = 1) : d157343 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13196, d157343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13196, d157343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro30224 (p : Pattern) (ha : d13260 p = 1) (hb : d152855 p = 1) : d157366 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13197 q = 1) (hb : d152855 q = 1) : d157344 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13197, d157344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30223 q ha hb
    | true =>
      simp only [d13197, d157344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13198 q = 1) (hb : d152855 q = 1) : d157345 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13198, d157345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13198, d157345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13257 q = 1) (hb : d152855 q = 1) : d157363 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13257, d157363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13257, d157363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13258 q = 1) (hb : d152855 q = 1) : d157364 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13258, d157364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13258, d157364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13259 q = 1) (hb : d152855 q = 1) : d157365 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13259, d157365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13259, d157365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13260 q = 1) (hb : d152855 q = 1) : d157366 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13260, d157366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13260, d157366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro30225 (p : Pattern) (ha : d13266 p = 1) (hb : d152855 p = 1) : d157372 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13261 q = 1) (hb : d152855 q = 1) : d157367 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13261, d157367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30224 q ha hb
    | true =>
      simp only [d13261, d157367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13262 q = 1) (hb : d152855 q = 1) : d157368 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13262, d157368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13262, d157368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13263 q = 1) (hb : d152855 q = 1) : d157369 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13263, d157369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13263, d157369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13264 q = 1) (hb : d152855 q = 1) : d157370 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13264, d157370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13264, d157370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13265 q = 1) (hb : d152855 q = 1) : d157371 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13265, d157371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13265, d157371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13266 q = 1) (hb : d152855 q = 1) : d157372 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d13266, d157372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13266, d157372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro30226 (p : Pattern) (ha : d13002 p = 1) (hb : d152855 p = 1) : d157177 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12968 q = 1) (hb : d152855 q = 1) : d157143 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12968, d157143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30208 q ha hb
    | true =>
      simp only [d12968, d157143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12969 q = 1) (hb : d152855 q = 1) : d157144 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12969, d157144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12969, d157144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12972 q = 1) (hb : d152855 q = 1) : d157147 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12972, d157147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30209 q ha hb
    | true =>
      simp only [d12972, d157147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12973 q = 1) (hb : d152855 q = 1) : d157148 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12973, d157148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12973, d157148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12974 q = 1) (hb : d152855 q = 1) : d157149 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12974, d157149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12974, d157149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12975 q = 1) (hb : d152855 q = 1) : d157150 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12975, d157150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12975, d157150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13001 q = 1) (hb : d152855 q = 1) : d157176 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13001, d157176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13001, d157176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d13002 q = 1) (hb : d152855 q = 1) : d157177 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13002, d157177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13002, d157177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro30227 (p : Pattern) (ha : d13004 p = 1) (hb : d152855 p = 1) : d157179 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12972 q = 1) (hb : d152855 q = 1) : d157147 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12972, d157147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30209 q ha hb
    | true =>
      simp only [d12972, d157147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12973 q = 1) (hb : d152855 q = 1) : d157148 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12973, d157148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12973, d157148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12978 q = 1) (hb : d152855 q = 1) : d157153 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12978, d157153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12978, d157153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12979 q = 1) (hb : d152855 q = 1) : d157154 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12979, d157154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12979, d157154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13003 q = 1) (hb : d152855 q = 1) : d157178 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13003, d157178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13003, d157178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13004 q = 1) (hb : d152855 q = 1) : d157179 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13004, d157179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13004, d157179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro30228 (p : Pattern) (ha : d13011 p = 1) (hb : d152855 p = 1) : d157186 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12968 q = 1) (hb : d152855 q = 1) : d157143 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12968, d157143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30208 q ha hb
    | true =>
      simp only [d12968, d157143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12969 q = 1) (hb : d152855 q = 1) : d157144 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12969, d157144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12969, d157144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12972 q = 1) (hb : d152855 q = 1) : d157147 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12972, d157147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30209 q ha hb
    | true =>
      simp only [d12972, d157147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12973 q = 1) (hb : d152855 q = 1) : d157148 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12973, d157148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12973, d157148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12974 q = 1) (hb : d152855 q = 1) : d157149 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12974, d157149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12974, d157149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13009 q = 1) (hb : d152855 q = 1) : d157184 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13009, d157184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13009, d157184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d13010 q = 1) (hb : d152855 q = 1) : d157185 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13010, d157185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13010, d157185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13011 q = 1) (hb : d152855 q = 1) : d157186 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13011, d157186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13011, d157186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro30229 (p : Pattern) (ha : d13014 p = 1) (hb : d152855 p = 1) : d157189 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12972 q = 1) (hb : d152855 q = 1) : d157147 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12972, d157147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30209 q ha hb
    | true =>
      simp only [d12972, d157147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12973 q = 1) (hb : d152855 q = 1) : d157148 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12973, d157148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12973, d157148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12978 q = 1) (hb : d152855 q = 1) : d157153 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12978, d157153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12978, d157153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13012 q = 1) (hb : d152855 q = 1) : d157187 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13012, d157187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13012, d157187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13013 q = 1) (hb : d152855 q = 1) : d157188 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13013, d157188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13013, d157188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13014 q = 1) (hb : d152855 q = 1) : d157189 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13014, d157189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13014, d157189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro30230 (p : Pattern) (ha : d1209 p = 1) (hb : d152854 p = 1) : d157193 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1208 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d823 q = 1) : d823 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1089 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1090 q = 1) (hb : d152852 q = 1) : d9759 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1090, d152852, d9759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d1090, d152852, d9759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d1 q = 1) (hb : d829 q = 1) : d829 q = 1 := by
    exact hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d538 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d830 q = 1) (hb : d152852 q = 1) : d25761 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d830, d152852, d25761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d830, d152852, d25761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d1091 q = 1) (hb : d152852 q = 1) : d25762 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d1091, d25762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1091, d25762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d152852 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d1092 q = 1) (hb : d152852 q = 1) : d25763 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d1092, d25763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1092, d25763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1209 q = 1) (hb : d152854 q = 1) : d157193 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d1209, d152854, d157193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1209, d152854, d157193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro30231 (p : Pattern) (ha : d13018 p = 1) (hb : d152855 p = 1) : d157199 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1210 q = 1) (hb : d152854 q = 1) : d157194 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1210, d157194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30230 q ha hb
    | true =>
      simp only [d1210, d157194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1211 q = 1) (hb : d152854 q = 1) : d157195 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1211, d157195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1211, d157195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1212 q = 1) (hb : d152854 q = 1) : d157196 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1212, d157196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1212, d157196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1213 q = 1) (hb : d152854 q = 1) : d157197 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1213, d157197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1213, d157197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1100 q = 1) (hb : d152854 q = 1) : d157113 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1100, d157113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30205 q ha hb
    | true =>
      simp only [d1100, d157113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1101 q = 1) (hb : d152854 q = 1) : d157114 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1101, d157114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1101, d157114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1102 q = 1) (hb : d152854 q = 1) : d157115 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1102, d157115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1102, d157115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1103 q = 1) (hb : d152854 q = 1) : d157116 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1103, d157116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1103, d157116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d1214 q = 1) (hb : d152854 q = 1) : d157198 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1214, d157198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1214, d157198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d13018 q = 1) (hb : d152855 q = 1) : d157199 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13018, d152855, d157199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d13018, d152855, d157199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro30232 (p : Pattern) (ha : d9813 p = 1) (hb : d152854 p = 1) : d157206 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d9812 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d9773 q = 1) : d9773 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d9453 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d9774 q = 1) (hb : d152852 q = 1) : d157203 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d9774, d152852, d157203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d9774, d152852, d157203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d152852 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d9775 q = 1) (hb : d152852 q = 1) : d157204 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d9775, d157204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9775, d157204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d9776 q = 1) (hb : d152852 q = 1) : d157205 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d9776, d157205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9776, d157205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h7 (q : Pattern) (ha : d9813 q = 1) (hb : d152854 q = 1) : d157206 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d9813, d152854, d157206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d9813, d152854, d157206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro30233 (p : Pattern) (ha : d13024 p = 1) (hb : d152854 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d9798 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d152852 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d13024 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d13024, d152854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d13024, d152854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro30234 (p : Pattern) (ha : d13030 p = 1) (hb : d152855 p = 1) : d157212 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9814 q = 1) (hb : d152854 q = 1) : d157207 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9814, d157207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30232 q ha hb
    | true =>
      simp only [d9814, d157207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9816 q = 1) (hb : d152854 q = 1) : d157208 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9816, d157208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d9816, d157208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d13022 q = 1) (hb : d152854 q = 1) : d157209 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13022, d157209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13022, d157209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d13023 q = 1) (hb : d152854 q = 1) : d157210 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13023, d157210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13023, d157210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13025 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30233 q ha hb
    | true =>
      simp only [d13025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13026 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13027 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d13028 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d13029 q = 1) (hb : d152854 q = 1) : d157211 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d13029, d157211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13029, d157211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d13030 q = 1) (hb : d152855 q = 1) : d157212 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13030, d152855, d157212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d13030, d152855, d157212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro30235 (p : Pattern) (ha : d13036 p = 1) (hb : d152855 p = 1) : d157218 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13019 q = 1) (hb : d152855 q = 1) : d157200 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13019, d157200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30231 q ha hb
    | true =>
      simp only [d13019, d157200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30206 q ha hb
  have h2 (q : Pattern) (ha : d13020 q = 1) (hb : d152855 q = 1) : d157201 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13020, d157201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13020, d157201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13021 q = 1) (hb : d152855 q = 1) : d157202 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13021, d157202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13021, d157202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d13031 q = 1) (hb : d152855 q = 1) : d157213 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13031, d157213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30206 q ha hb
    | true =>
      simp only [d13031, d157213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30234 q ha hb
  have h5 (q : Pattern) (ha : d13032 q = 1) (hb : d152855 q = 1) : d157214 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13032, d157214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13032, d157214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13033 q = 1) (hb : d152855 q = 1) : d157215 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13033, d157215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13033, d157215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d13034 q = 1) (hb : d152855 q = 1) : d157216 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13034, d157216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13034, d157216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12957 q = 1) (hb : d152855 q = 1) : d157131 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12957, d157131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30206 q ha hb
    | true =>
      simp only [d12957, d157131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30202 q ha hb
  have h9 (q : Pattern) (ha : d12958 q = 1) (hb : d152855 q = 1) : d157132 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12958, d157132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12958, d157132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d12959 q = 1) (hb : d152855 q = 1) : d157133 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12959, d157133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12959, d157133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d5024 q = 1) (hb : d152855 q = 1) : d157136 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d5024, d157136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30202 q ha hb
    | true =>
      simp only [d5024, d157136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30204 q ha hb
  have h12 (q : Pattern) (ha : d5025 q = 1) (hb : d152855 q = 1) : d157137 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d5025, d157137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5025, d157137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d5026 q = 1) (hb : d152855 q = 1) : d157138 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d5026, d157138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5026, d157138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d12960 q = 1) (hb : d152855 q = 1) : d157139 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12960, d157139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d12960, d157139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d13035 q = 1) (hb : d152855 q = 1) : d157217 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13035, d157217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13035, d157217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d13036 q = 1) (hb : d152855 q = 1) : d157218 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13036, d157218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d13036, d157218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro30236 (p : Pattern) (ha : d13046 p = 1) (hb : d152855 p = 1) : d157224 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13037 q = 1) (hb : d152855 q = 1) : d157219 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13037, d157219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30235 q ha hb
    | true =>
      simp only [d13037, d157219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13038 q = 1) (hb : d152855 q = 1) : d157220 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13038, d157220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13038, d157220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13041 q = 1) (hb : d152855 q = 1) : d157143 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13041, d157143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30216 q ha hb
    | true =>
      simp only [d13041, d157143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13042 q = 1) (hb : d152855 q = 1) : d157144 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13042, d157144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13042, d157144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13043 q = 1) (hb : d152855 q = 1) : d157221 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13043, d157221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13043, d157221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13044 q = 1) (hb : d152855 q = 1) : d157222 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13044, d157222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13044, d157222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13045 q = 1) (hb : d152855 q = 1) : d157223 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13045, d157223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13045, d157223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13046 q = 1) (hb : d152855 q = 1) : d157224 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13046, d157224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13046, d157224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro30237 (p : Pattern) (ha : d13091 p = 1) (hb : d152855 p = 1) : d157230 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12968 q = 1) (hb : d152855 q = 1) : d157143 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12968, d157143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30208 q ha hb
    | true =>
      simp only [d12968, d157143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12969 q = 1) (hb : d152855 q = 1) : d157144 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12969, d157144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12969, d157144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13088 q = 1) (hb : d152855 q = 1) : d157227 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13088, d157227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13088, d157227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13089 q = 1) (hb : d152855 q = 1) : d157228 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13089, d157228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13089, d157228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13090 q = 1) (hb : d152855 q = 1) : d157229 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13090, d157229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13090, d157229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13091 q = 1) (hb : d152855 q = 1) : d157230 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13091, d157230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13091, d157230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro30238 (p : Pattern) (ha : d115400 p = 1) (hb : d152855 p = 1) : d157236 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13005 q = 1) (hb : d152855 q = 1) : d157180 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13005, d157180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30226 q ha hb
    | true =>
      simp only [d13005, d157180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30227 q ha hb
  have h2 (q : Pattern) (ha : d13006 q = 1) (hb : d152855 q = 1) : d157181 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13006, d157181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13006, d157181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13007 q = 1) (hb : d152855 q = 1) : d157182 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13007, d157182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13007, d157182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13008 q = 1) (hb : d152855 q = 1) : d157183 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13008, d157183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13008, d157183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13015 q = 1) (hb : d152855 q = 1) : d157190 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13015, d157190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30228 q ha hb
    | true =>
      simp only [d13015, d157190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30229 q ha hb
  have h6 (q : Pattern) (ha : d13016 q = 1) (hb : d152855 q = 1) : d157191 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13016, d157191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13016, d157191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d13017 q = 1) (hb : d152855 q = 1) : d157192 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13017, d157192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13017, d157192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13051 q = 1) (hb : d152855 q = 1) : d157225 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13051, d157225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30236 q ha hb
    | true =>
      simp only [d13051, d157225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30217 q ha hb
  have h9 (q : Pattern) (ha : d115396 q = 1) (hb : d152855 q = 1) : d157226 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115396, d157226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d115396, d157226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d13092 q = 1) (hb : d152855 q = 1) : d157231 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13092, d157231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30237 q ha hb
    | true =>
      simp only [d13092, d157231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d13093 q = 1) (hb : d152855 q = 1) : d157232 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13093, d157232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d13093, d157232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d115397 q = 1) (hb : d152855 q = 1) : d157233 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115397, d157233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d115397, d157233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d115398 q = 1) (hb : d152855 q = 1) : d157234 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115398, d157234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d115398, d157234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d115399 q = 1) (hb : d152855 q = 1) : d157235 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115399, d157235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115399, d157235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d115400 q = 1) (hb : d152855 q = 1) : d157236 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115400, d157236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115400, d157236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro30239 (p : Pattern) (ha : d13098 p = 1) (hb : d152855 p = 1) : d157237 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12968 q = 1) (hb : d152855 q = 1) : d157143 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12968, d157143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30208 q ha hb
    | true =>
      simp only [d12968, d157143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12969 q = 1) (hb : d152855 q = 1) : d157144 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12969, d157144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12969, d157144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12972 q = 1) (hb : d152855 q = 1) : d157147 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12972, d157147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30209 q ha hb
    | true =>
      simp only [d12972, d157147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12973 q = 1) (hb : d152855 q = 1) : d157148 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12973, d157148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12973, d157148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12974 q = 1) (hb : d152855 q = 1) : d157149 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12974, d157149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12974, d157149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12975 q = 1) (hb : d152855 q = 1) : d157150 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12975, d157150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12975, d157150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13001 q = 1) (hb : d152855 q = 1) : d157176 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13001, d157176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13001, d157176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d13098 q = 1) (hb : d152855 q = 1) : d157237 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13098, d157237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13098, d157237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro30240 (p : Pattern) (ha : d13099 p = 1) (hb : d152855 p = 1) : d157238 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12972 q = 1) (hb : d152855 q = 1) : d157147 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12972, d157147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30209 q ha hb
    | true =>
      simp only [d12972, d157147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12973 q = 1) (hb : d152855 q = 1) : d157148 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12973, d157148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12973, d157148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12978 q = 1) (hb : d152855 q = 1) : d157153 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12978, d157153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12978, d157153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12979 q = 1) (hb : d152855 q = 1) : d157154 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12979, d157154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12979, d157154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13003 q = 1) (hb : d152855 q = 1) : d157178 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13003, d157178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13003, d157178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13099 q = 1) (hb : d152855 q = 1) : d157238 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13099, d157238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13099, d157238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro30241 (p : Pattern) (ha : d13104 p = 1) (hb : d152855 p = 1) : d157243 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12968 q = 1) (hb : d152855 q = 1) : d157143 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12968, d157143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30208 q ha hb
    | true =>
      simp only [d12968, d157143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12969 q = 1) (hb : d152855 q = 1) : d157144 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12969, d157144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12969, d157144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12972 q = 1) (hb : d152855 q = 1) : d157147 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12972, d157147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30209 q ha hb
    | true =>
      simp only [d12972, d157147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12973 q = 1) (hb : d152855 q = 1) : d157148 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12973, d157148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12973, d157148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12974 q = 1) (hb : d152855 q = 1) : d157149 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12974, d157149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12974, d157149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13009 q = 1) (hb : d152855 q = 1) : d157184 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13009, d157184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13009, d157184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d13010 q = 1) (hb : d152855 q = 1) : d157185 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13010, d157185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13010, d157185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13104 q = 1) (hb : d152855 q = 1) : d157243 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13104, d157243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13104, d157243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro30242 (p : Pattern) (ha : d13105 p = 1) (hb : d152855 p = 1) : d157244 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12972 q = 1) (hb : d152855 q = 1) : d157147 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12972, d157147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30209 q ha hb
    | true =>
      simp only [d12972, d157147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12973 q = 1) (hb : d152855 q = 1) : d157148 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12973, d157148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12973, d157148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12978 q = 1) (hb : d152855 q = 1) : d157153 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12978, d157153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12978, d157153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13012 q = 1) (hb : d152855 q = 1) : d157187 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13012, d157187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13012, d157187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13013 q = 1) (hb : d152855 q = 1) : d157188 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13013, d157188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13013, d157188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13105 q = 1) (hb : d152855 q = 1) : d157244 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13105, d157244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13105, d157244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro30243 (p : Pattern) (ha : d13109 p = 1) (hb : d152855 p = 1) : d157248 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13037 q = 1) (hb : d152855 q = 1) : d157219 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13037, d157219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30235 q ha hb
    | true =>
      simp only [d13037, d157219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13038 q = 1) (hb : d152855 q = 1) : d157220 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13038, d157220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13038, d157220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13041 q = 1) (hb : d152855 q = 1) : d157143 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13041, d157143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30216 q ha hb
    | true =>
      simp only [d13041, d157143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13042 q = 1) (hb : d152855 q = 1) : d157144 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13042, d157144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13042, d157144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13043 q = 1) (hb : d152855 q = 1) : d157221 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13043, d157221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13043, d157221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13044 q = 1) (hb : d152855 q = 1) : d157222 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13044, d157222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13044, d157222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13045 q = 1) (hb : d152855 q = 1) : d157223 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13045, d157223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13045, d157223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13109 q = 1) (hb : d152855 q = 1) : d157248 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13109, d157248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13109, d157248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro30244 (p : Pattern) (ha : d13110 p = 1) (hb : d152855 p = 1) : d157165 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13041 q = 1) (hb : d152855 q = 1) : d157143 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13041, d157143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30216 q ha hb
    | true =>
      simp only [d13041, d157143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13042 q = 1) (hb : d152855 q = 1) : d157144 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13042, d157144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13042, d157144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12972 q = 1) (hb : d152855 q = 1) : d157147 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12972, d157147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30209 q ha hb
    | true =>
      simp only [d12972, d157147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12973 q = 1) (hb : d152855 q = 1) : d157148 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12973, d157148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12973, d157148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13047 q = 1) (hb : d152855 q = 1) : d157149 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13047, d157149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13047, d157149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13048 q = 1) (hb : d152855 q = 1) : d157150 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13048, d157150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13048, d157150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13049 q = 1) (hb : d152855 q = 1) : d157151 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13049, d157151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13049, d157151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13110 q = 1) (hb : d152855 q = 1) : d157165 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13110, d157165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13110, d157165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro30245 (p : Pattern) (ha : d13116 p = 1) (hb : d152855 p = 1) : d157251 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12968 q = 1) (hb : d152855 q = 1) : d157143 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12968, d157143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30208 q ha hb
    | true =>
      simp only [d12968, d157143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12969 q = 1) (hb : d152855 q = 1) : d157144 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12969, d157144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12969, d157144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13088 q = 1) (hb : d152855 q = 1) : d157227 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13088, d157227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13088, d157227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13089 q = 1) (hb : d152855 q = 1) : d157228 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13089, d157228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13089, d157228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13090 q = 1) (hb : d152855 q = 1) : d157229 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13090, d157229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13090, d157229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13116 q = 1) (hb : d152855 q = 1) : d157251 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13116, d157251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13116, d157251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro30246 (p : Pattern) (ha : d115405 p = 1) (hb : d152855 p = 1) : d157257 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13005 q = 1) (hb : d152855 q = 1) : d157180 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13005, d157180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30226 q ha hb
    | true =>
      simp only [d13005, d157180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30227 q ha hb
  have h2 (q : Pattern) (ha : d13006 q = 1) (hb : d152855 q = 1) : d157181 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13006, d157181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13006, d157181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13007 q = 1) (hb : d152855 q = 1) : d157182 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13007, d157182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13007, d157182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13008 q = 1) (hb : d152855 q = 1) : d157183 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13008, d157183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13008, d157183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13015 q = 1) (hb : d152855 q = 1) : d157190 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13015, d157190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30228 q ha hb
    | true =>
      simp only [d13015, d157190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30229 q ha hb
  have h6 (q : Pattern) (ha : d13016 q = 1) (hb : d152855 q = 1) : d157191 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13016, d157191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13016, d157191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d13017 q = 1) (hb : d152855 q = 1) : d157192 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13017, d157192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13017, d157192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13051 q = 1) (hb : d152855 q = 1) : d157225 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13051, d157225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30236 q ha hb
    | true =>
      simp only [d13051, d157225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30217 q ha hb
  have h9 (q : Pattern) (ha : d115396 q = 1) (hb : d152855 q = 1) : d157226 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115396, d157226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d115396, d157226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d13092 q = 1) (hb : d152855 q = 1) : d157231 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13092, d157231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30237 q ha hb
    | true =>
      simp only [d13092, d157231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d13093 q = 1) (hb : d152855 q = 1) : d157232 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13093, d157232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d13093, d157232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d115397 q = 1) (hb : d152855 q = 1) : d157233 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115397, d157233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d115397, d157233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d115398 q = 1) (hb : d152855 q = 1) : d157234 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115398, d157234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d115398, d157234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d115399 q = 1) (hb : d152855 q = 1) : d157235 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115399, d157235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115399, d157235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d13100 q = 1) (hb : d152855 q = 1) : d157239 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13100, d157239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30239 q ha hb
    | true =>
      simp only [d13100, d157239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30240 q ha hb
  have h16 (q : Pattern) (ha : d13101 q = 1) (hb : d152855 q = 1) : d157240 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13101, d157240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13101, d157240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d13102 q = 1) (hb : d152855 q = 1) : d157241 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13102, d157241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d13102, d157241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d13103 q = 1) (hb : d152855 q = 1) : d157242 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13103, d157242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13103, d157242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d13106 q = 1) (hb : d152855 q = 1) : d157245 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13106, d157245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30241 q ha hb
    | true =>
      simp only [d13106, d157245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30242 q ha hb
  have h20 (q : Pattern) (ha : d13107 q = 1) (hb : d152855 q = 1) : d157246 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13107, d157246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13107, d157246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d13108 q = 1) (hb : d152855 q = 1) : d157247 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13108, d157247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d13108, d157247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d13111 q = 1) (hb : d152855 q = 1) : d157249 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13111, d157249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30243 q ha hb
    | true =>
      simp only [d13111, d157249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30244 q ha hb
  have h23 (q : Pattern) (ha : d115401 q = 1) (hb : d152855 q = 1) : d157250 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115401, d157250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d115401, d157250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d13117 q = 1) (hb : d152855 q = 1) : d157252 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13117, d157252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30245 q ha hb
    | true =>
      simp only [d13117, d157252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d13118 q = 1) (hb : d152855 q = 1) : d157253 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13118, d157253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d13118, d157253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d115402 q = 1) (hb : d152855 q = 1) : d157254 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115402, d157254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d115402, d157254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d115403 q = 1) (hb : d152855 q = 1) : d157255 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115403, d157255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d115403, d157255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d115404 q = 1) (hb : d152855 q = 1) : d157256 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115404, d157256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d115404, d157256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d115405 q = 1) (hb : d152855 q = 1) : d157257 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115405, d157257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d115405, d157257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro30247 (p : Pattern) (ha : d115412 p = 1) (hb : d152855 p = 1) : d157277 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13111 q = 1) (hb : d152855 q = 1) : d157249 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13111, d157249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30243 q ha hb
    | true =>
      simp only [d13111, d157249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30244 q ha hb
  have h2 (q : Pattern) (ha : d115401 q = 1) (hb : d152855 q = 1) : d157250 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115401, d157250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115401, d157250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d13117 q = 1) (hb : d152855 q = 1) : d157252 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13117, d157252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30245 q ha hb
    | true =>
      simp only [d13117, d157252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13118 q = 1) (hb : d152855 q = 1) : d157253 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13118, d157253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13118, d157253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d115402 q = 1) (hb : d152855 q = 1) : d157254 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115402, d157254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115402, d157254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115410 q = 1) (hb : d152855 q = 1) : d157275 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115410, d157275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115410, d157275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d115411 q = 1) (hb : d152855 q = 1) : d157276 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115411, d157276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115411, d157276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d115412 q = 1) (hb : d152855 q = 1) : d157277 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115412, d157277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115412, d157277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro30248 (p : Pattern) (ha : d6355 p = 1) (hb : d152855 p = 1) : d157324 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6350 q = 1) (hb : d152854 q = 1) : d157314 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d6350, d157314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6350, d157314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30203 q ha hb
  have h2 (q : Pattern) (ha : d5018 q = 1) (hb : d152854 q = 1) : d157125 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5018, d157125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30203 q ha hb
    | true =>
      simp only [d5018, d157125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d6351 q = 1) (hb : d152854 q = 1) : d157315 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d6351, d157315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6351, d157315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d5019 q = 1) (hb : d152854 q = 1) : d157126 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5019, d157126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5019, d157126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6352 q = 1) (hb : d152854 q = 1) : d157316 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d6352, d157316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6352, d157316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6353 q = 1) (hb : d152854 q = 1) : d157317 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d6353, d157317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6353, d157317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d6354 q = 1) (hb : d152854 q = 1) : d157323 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d6354, d157323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6354, d157323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d6355 q = 1) (hb : d152855 q = 1) : d157324 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d6355, d152855, d157324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6355, d152855, d157324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro30249 (p : Pattern) (ha : d13155 p = 1) (hb : d152855 p = 1) : d157294 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1376 q = 1) (hb : d152854 q = 1) : d157285 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1376, d157285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1376, d157285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30230 q ha hb
  have h2 (q : Pattern) (ha : d1210 q = 1) (hb : d152854 q = 1) : d157194 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1210, d157194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30230 q ha hb
    | true =>
      simp only [d1210, d157194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1377 q = 1) (hb : d152854 q = 1) : d157286 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1377, d157286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1377, d157286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1211 q = 1) (hb : d152854 q = 1) : d157195 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1211, d157195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1211, d157195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1378 q = 1) (hb : d152854 q = 1) : d157287 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1378, d157287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1378, d157287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1379 q = 1) (hb : d152854 q = 1) : d157288 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1379, d157288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1379, d157288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1380 q = 1) (hb : d152854 q = 1) : d157289 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1380, d157289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1380, d157289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30205 q ha hb
  have h8 (q : Pattern) (ha : d1100 q = 1) (hb : d152854 q = 1) : d157113 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1100, d157113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30205 q ha hb
    | true =>
      simp only [d1100, d157113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d1381 q = 1) (hb : d152854 q = 1) : d157290 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1381, d157290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1381, d157290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1101 q = 1) (hb : d152854 q = 1) : d157114 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1101, d157114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1101, d157114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d1382 q = 1) (hb : d152854 q = 1) : d157291 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1382, d157291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d1382, d157291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d1383 q = 1) (hb : d152854 q = 1) : d157292 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1383, d157292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d1383, d157292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d1384 q = 1) (hb : d152854 q = 1) : d157293 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1384, d157293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1384, d157293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d13155 q = 1) (hb : d152855 q = 1) : d157294 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13155, d152855, d157294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d13155, d152855, d157294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
end NetHack.Soko22Hazard87
