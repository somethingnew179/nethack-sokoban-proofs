import NetHack.Soko22Hazard87.AndIntroBlocks0186
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro46750 (p : Pattern) (ha : d116753 p = 1) (hb : d150320 p = 1) : d197135 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d116753 q = 1) (hb : d150315 q = 1) : d197130 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d150315, d197130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46749 q ha hb
    | true =>
      simp only [d150315, d197130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d116753 q = 1) (hb : d150316 q = 1) : d197131 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d150316, d197131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150316, d197131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d116753 q = 1) (hb : d150317 q = 1) : d197132 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d150317, d197132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150317, d197132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d116753 q = 1) (hb : d150318 q = 1) : d197133 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d150318, d197133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150318, d197133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d116753 q = 1) (hb : d150319 q = 1) : d197134 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d150319, d197134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150319, d197134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d116753 q = 1) (hb : d150320 q = 1) : d197135 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d150320, d197135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150320, d197135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro46751 (p : Pattern) (ha : d116753 p = 1) (hb : d150326 p = 1) : d197141 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d116753 q = 1) (hb : d150321 q = 1) : d197136 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d150321, d197136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46750 q ha hb
    | true =>
      simp only [d150321, d197136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d116753 q = 1) (hb : d150322 q = 1) : d197137 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d150322, d197137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150322, d197137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d116753 q = 1) (hb : d150323 q = 1) : d197138 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d150323, d197138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150323, d197138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d116753 q = 1) (hb : d150324 q = 1) : d197139 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d150324, d197139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150324, d197139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d116753 q = 1) (hb : d150325 q = 1) : d197140 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d150325, d197140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150325, d197140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d116753 q = 1) (hb : d150326 q = 1) : d197141 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d150326, d197141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150326, d197141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro46752 (p : Pattern) (ha : d96224 p = 1) (hb : d120072 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96220 q = 1) (hb : d120067 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d96220, d120067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35442 q ha hb
    | true =>
      simp only [d96220, d120067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d96221 q = 1) (hb : d120068 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d96221, d120068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96221, d120068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d96222 q = 1) (hb : d120069 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d96222, d120069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96222, d120069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d96222 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d96222 q = 1) (hb : d120070 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d120070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d120070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d96223 q = 1) (hb : d120071 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d96223, d120071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d96223, d120071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d96224 q = 1) (hb : d120072 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d96224, d120072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d96224, d120072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro46753 (p : Pattern) (ha : d96230 p = 1) (hb : d120078 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96225 q = 1) (hb : d120073 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d96225, d120073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46752 q ha hb
    | true =>
      simp only [d96225, d120073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d96226 q = 1) (hb : d120074 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d96226, d120074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96226, d120074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d96227 q = 1) (hb : d120075 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d96227, d120075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d96227, d120075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d96228 q = 1) (hb : d120076 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d96228, d120076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d96228, d120076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d96229 q = 1) (hb : d120077 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d96229, d120077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d96229, d120077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d96230 q = 1) (hb : d120078 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d96230, d120078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96230, d120078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro46754 (p : Pattern) (ha : d96236 p = 1) (hb : d120084 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96231 q = 1) (hb : d120079 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d96231, d120079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46753 q ha hb
    | true =>
      simp only [d96231, d120079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d96232 q = 1) (hb : d120080 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d96232, d120080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d96232, d120080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d96233 q = 1) (hb : d120081 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d96233, d120081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d96233, d120081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d96234 q = 1) (hb : d120082 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d96234, d120082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96234, d120082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d96235 q = 1) (hb : d120083 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d96235, d120083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96235, d120083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d96236 q = 1) (hb : d120084 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d96236, d120084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96236, d120084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro46755 (p : Pattern) (ha : d96237 p = 1) (hb : d120085 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96225 q = 1) (hb : d120073 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d96225, d120073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46752 q ha hb
    | true =>
      simp only [d96225, d120073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d96226 q = 1) (hb : d120074 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d96226, d120074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96226, d120074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d96227 q = 1) (hb : d120075 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d96227, d120075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d96227, d120075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d96228 q = 1) (hb : d120076 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d96228, d120076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d96228, d120076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d96229 q = 1) (hb : d120077 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d96229, d120077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d96229, d120077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d96237 q = 1) (hb : d120085 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d96237, d120085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d96237, d120085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro46756 (p : Pattern) (ha : d96243 p = 1) (hb : d120091 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96231 q = 1) (hb : d120079 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d96231, d120079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46753 q ha hb
    | true =>
      simp only [d96231, d120079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d96232 q = 1) (hb : d120080 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d96232, d120080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d96232, d120080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d96233 q = 1) (hb : d120081 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d96233, d120081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d96233, d120081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d96234 q = 1) (hb : d120082 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d96234, d120082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96234, d120082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d96235 q = 1) (hb : d120083 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d96235, d120083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96235, d120083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d96238 q = 1) (hb : d120086 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d96238, d120086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46755 q ha hb
    | true =>
      simp only [d96238, d120086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d96239 q = 1) (hb : d120087 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d96239, d120087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d96239, d120087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d96240 q = 1) (hb : d120088 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d96240, d120088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d96240, d120088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d96241 q = 1) (hb : d120089 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d96241, d120089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96241, d120089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d96242 q = 1) (hb : d120090 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d96242, d120090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96242, d120090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d96243 q = 1) (hb : d120091 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d96243, d120091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d96243, d120091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro46757 (p : Pattern) (ha : d96248 p = 1) (hb : d120096 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96238 q = 1) (hb : d120086 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d96238, d120086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46755 q ha hb
    | true =>
      simp only [d96238, d120086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d96239 q = 1) (hb : d120087 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d96239, d120087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d96239, d120087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d96240 q = 1) (hb : d120088 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d96240, d120088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d96240, d120088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d96241 q = 1) (hb : d120089 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d96241, d120089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96241, d120089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d96242 q = 1) (hb : d120090 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d96242, d120090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96242, d120090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d96248 q = 1) (hb : d120096 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d96248, d120096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96248, d120096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro46758 (p : Pattern) (ha : d96258 p = 1) (hb : d120108 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96254 q = 1) (hb : d120103 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d96254, d120103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35449 q ha hb
    | true =>
      simp only [d96254, d120103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d96255 q = 1) (hb : d120104 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d96255, d120104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96255, d120104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d96256 q = 1) (hb : d120105 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d96256, d120105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96256, d120105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d96256 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d96256 q = 1) (hb : d120106 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d120106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d120106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d96257 q = 1) (hb : d120107 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d96257, d120107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d96257, d120107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d96258 q = 1) (hb : d120108 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d96258, d120108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d96258, d120108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro46759 (p : Pattern) (ha : d96264 p = 1) (hb : d120114 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96259 q = 1) (hb : d120109 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d96259, d120109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46758 q ha hb
    | true =>
      simp only [d96259, d120109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d96260 q = 1) (hb : d120110 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d96260, d120110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96260, d120110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d96261 q = 1) (hb : d120111 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d96261, d120111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d96261, d120111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d96262 q = 1) (hb : d120112 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d96262, d120112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d96262, d120112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d96263 q = 1) (hb : d120113 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d96263, d120113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d96263, d120113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d96264 q = 1) (hb : d120114 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d96264, d120114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d96264, d120114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro46760 (p : Pattern) (ha : d96270 p = 1) (hb : d120120 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96265 q = 1) (hb : d120115 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d96265, d120115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46759 q ha hb
    | true =>
      simp only [d96265, d120115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d96266 q = 1) (hb : d120116 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d96266, d120116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d96266, d120116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d96267 q = 1) (hb : d120117 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d96267, d120117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d96267, d120117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d96268 q = 1) (hb : d120118 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d96268, d120118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96268, d120118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d96269 q = 1) (hb : d120119 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d96269, d120119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96269, d120119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d96270 q = 1) (hb : d120120 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d96270, d120120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96270, d120120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro46761 (p : Pattern) (ha : d96276 p = 1) (hb : d120126 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96244 q = 1) (hb : d120092 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d96244, d120092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46754 q ha hb
    | true =>
      simp only [d96244, d120092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46756 q ha hb
  have h2 (q : Pattern) (ha : d96245 q = 1) (hb : d120093 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d96245, d120093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d96245, d120093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d96246 q = 1) (hb : d120094 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d96246, d120094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d96246, d120094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d96247 q = 1) (hb : d120095 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d96247, d120095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96247, d120095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d96249 q = 1) (hb : d120097 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d96249, d120097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96249, d120097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46757 q ha hb
  have h6 (q : Pattern) (ha : d96250 q = 1) (hb : d120098 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d96250, d120098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d96250, d120098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d96251 q = 1) (hb : d120099 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d96251, d120099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d96251, d120099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d96252 q = 1) (hb : d120100 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d96252, d120100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d96252, d120100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d96253 q = 1) (hb : d120101 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d96253, d120101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d96253, d120101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d96271 q = 1) (hb : d120121 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d96271, d120121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96271, d120121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46760 q ha hb
  have h11 (q : Pattern) (ha : d96272 q = 1) (hb : d120122 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d96272, d120122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d96272, d120122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d96273 q = 1) (hb : d120123 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d96273, d120123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d96273, d120123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d96274 q = 1) (hb : d120124 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d96274, d120124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d96274, d120124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d96275 q = 1) (hb : d120125 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d96275, d120125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d96275, d120125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d96276 q = 1) (hb : d120126 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d96276, d120126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d96276, d120126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro46762 (p : Pattern) (ha : d96286 p = 1) (hb : d120136 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96231 q = 1) (hb : d120079 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d96231, d120079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46753 q ha hb
    | true =>
      simp only [d96231, d120079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d96282 q = 1) (hb : d120132 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d96282, d120132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96282, d120132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d96283 q = 1) (hb : d120133 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d96283, d120133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d96283, d120133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d96284 q = 1) (hb : d120134 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d96284, d120134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96284, d120134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d96285 q = 1) (hb : d120135 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d96285, d120135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96285, d120135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d96286 q = 1) (hb : d120136 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d96286, d120136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96286, d120136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro46763 (p : Pattern) (ha : d96293 p = 1) (hb : d120143 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96231 q = 1) (hb : d120079 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d96231, d120079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46753 q ha hb
    | true =>
      simp only [d96231, d120079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d96282 q = 1) (hb : d120132 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d96282, d120132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96282, d120132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d96283 q = 1) (hb : d120133 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d96283, d120133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d96283, d120133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d96284 q = 1) (hb : d120134 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d96284, d120134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96284, d120134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d96285 q = 1) (hb : d120135 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d96285, d120135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96285, d120135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d96238 q = 1) (hb : d120086 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d96238, d120086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46755 q ha hb
    | true =>
      simp only [d96238, d120086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d96289 q = 1) (hb : d120139 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d96289, d120139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96289, d120139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d96290 q = 1) (hb : d120140 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d96290, d120140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d96290, d120140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d96291 q = 1) (hb : d120141 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d96291, d120141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96291, d120141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d96292 q = 1) (hb : d120142 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d96292, d120142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96292, d120142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d96293 q = 1) (hb : d120143 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d96293, d120143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d96293, d120143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro46764 (p : Pattern) (ha : d96298 p = 1) (hb : d120148 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96225 q = 1) (hb : d120073 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d96225, d120073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46752 q ha hb
    | true =>
      simp only [d96225, d120073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d96226 q = 1) (hb : d120074 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d96226, d120074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96226, d120074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d96227 q = 1) (hb : d120075 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d96227, d120075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d96227, d120075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d96228 q = 1) (hb : d120076 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d96228, d120076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d96228, d120076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d96297 q = 1) (hb : d120147 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d96297, d120147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96297, d120147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d96298 q = 1) (hb : d120148 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d96298, d120148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96298, d120148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro46765 (p : Pattern) (ha : d96305 p = 1) (hb : d120155 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96225 q = 1) (hb : d120073 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d96225, d120073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46752 q ha hb
    | true =>
      simp only [d96225, d120073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d96226 q = 1) (hb : d120074 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d96226, d120074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96226, d120074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d96227 q = 1) (hb : d120075 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d96227, d120075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d96227, d120075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d96303 q = 1) (hb : d120153 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d96303, d120153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96303, d120153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d96304 q = 1) (hb : d120154 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d96304, d120154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d96304, d120154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d96305 q = 1) (hb : d120155 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d96305, d120155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96305, d120155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro46766 (p : Pattern) (ha : d5450 p = 1) (hb : d51989 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d133 q = 1) (hb : d51984 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d133, d51984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18 q ha hb
    | true =>
      simp only [d133, d51984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d134 q = 1) (hb : d51985 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d134, d51985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d134, d51985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d19 q = 1) (hb : d51871 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d19, d51871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1 q ha hb
    | true =>
      simp only [d19, d51871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20 q = 1) (hb : d51872 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d20, d51872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20, d51872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d135 q = 1) (hb : d51986 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d135, d51986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d135, d51986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d51873 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d5448 q = 1) (hb : d51987 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d5448, d51987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5448, d51987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d5449 q = 1) (hb : d51988 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d5449, d51988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d5449, d51988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d51875 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d5450 q = 1) (hb : d51989 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d5450, d51989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d5450, d51989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro46767 (p : Pattern) (ha : d51994 p = 1) (hb : d196073 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d51994 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d5451 q = 1) (hb : d51990 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5451, d51990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46766 q ha hb
    | true =>
      simp only [d5451, d51990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d5452 q = 1) (hb : d51991 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5452, d51991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5452, d51991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d5453 q = 1) (hb : d51992 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d5453, d51992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5453, d51992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d5454 q = 1) (hb : d51993 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d5454, d51993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5454, d51993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d25 q = 1) (hb : d51877 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25, d51877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2 q ha hb
    | true =>
      simp only [d25, d51877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d26 q = 1) (hb : d51878 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26, d51878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d26, d51878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d27 q = 1) (hb : d51879 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d27, d51879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d27, d51879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d28 q = 1) (hb : d51880 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d28, d51880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d28, d51880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d20995 q = 1) (hb : d51994 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d20995, d51994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20995, d51994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d51994 q = 1) (hb : d196073 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d196073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d196073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro46768 (p : Pattern) (ha : d96313 p = 1) (hb : d196079 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96309 q = 1) (hb : d196074 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d96309, d196074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46767 q ha hb
    | true =>
      simp only [d96309, d196074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35442 q ha hb
  have h2 (q : Pattern) (ha : d96310 q = 1) (hb : d196075 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d96310, d196075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96310, d196075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d96311 q = 1) (hb : d196076 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d96311, d196076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96311, d196076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d96311 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d96311 q = 1) (hb : d196077 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d196077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d196077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d96220 q = 1) (hb : d120067 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d96220, d120067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35442 q ha hb
    | true =>
      simp only [d96220, d120067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d96221 q = 1) (hb : d120068 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d96221, d120068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96221, d120068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d96222 q = 1) (hb : d120069 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d96222, d120069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96222, d120069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d96222 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d96222 q = 1) (hb : d120070 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d120070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d120070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d96312 q = 1) (hb : d196078 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d96312, d196078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d96312, d196078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d96313 q = 1) (hb : d196079 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d96313, d196079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d96313, d196079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h12 p ha hb
theorem andIntro46769 (p : Pattern) (ha : d96319 p = 1) (hb : d196085 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96314 q = 1) (hb : d196080 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d96314, d196080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46768 q ha hb
    | true =>
      simp only [d96314, d196080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d96315 q = 1) (hb : d196081 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d96315, d196081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96315, d196081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d96225 q = 1) (hb : d120073 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d96225, d120073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46752 q ha hb
    | true =>
      simp only [d96225, d120073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d96226 q = 1) (hb : d120074 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d96226, d120074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96226, d120074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d96316 q = 1) (hb : d196082 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d96316, d196082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d96316, d196082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d96317 q = 1) (hb : d196083 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d96317, d196083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d96317, d196083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d96318 q = 1) (hb : d196084 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d96318, d196084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d96318, d196084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d96319 q = 1) (hb : d196085 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d96319, d196085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96319, d196085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro46770 (p : Pattern) (ha : d96325 p = 1) (hb : d196091 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96299 q = 1) (hb : d120149 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d96299, d120149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46764 q ha hb
    | true =>
      simp only [d96299, d120149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d96300 q = 1) (hb : d120150 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d96300, d120150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96300, d120150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d96301 q = 1) (hb : d120151 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d96301, d120151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d96301, d120151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d96302 q = 1) (hb : d120152 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d96302, d120152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96302, d120152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d96306 q = 1) (hb : d120156 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d96306, d120156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46765 q ha hb
    | true =>
      simp only [d96306, d120156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d96307 q = 1) (hb : d120157 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d96307, d120157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96307, d120157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d96308 q = 1) (hb : d120158 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d96308, d120158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d96308, d120158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d96320 q = 1) (hb : d196086 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d96320, d196086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46769 q ha hb
    | true =>
      simp only [d96320, d196086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46753 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d96231 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d96321 q = 1) (hb : d196087 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d96321, d196087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d96321, d196087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d96231 q = 1) (hb : d120079 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d96231, d120079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46753 q ha hb
    | true =>
      simp only [d96231, d120079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d96232 q = 1) (hb : d120080 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d96232, d120080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d96232, d120080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d96322 q = 1) (hb : d196088 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d96322, d196088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d96322, d196088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d96323 q = 1) (hb : d196089 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d96323, d196089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d96323, d196089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d96324 q = 1) (hb : d196090 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d96324, d196090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d96324, d196090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d96325 q = 1) (hb : d196091 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d96325, d196091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96325, d196091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro46771 (p : Pattern) (ha : d96326 p = 1) (hb : d120178 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96225 q = 1) (hb : d120073 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d96225, d120073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46752 q ha hb
    | true =>
      simp only [d96225, d120073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d96226 q = 1) (hb : d120074 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d96226, d120074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96226, d120074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d96227 q = 1) (hb : d120075 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d96227, d120075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d96227, d120075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d96228 q = 1) (hb : d120076 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d96228, d120076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d96228, d120076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d96297 q = 1) (hb : d120147 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d96297, d120147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96297, d120147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d96326 q = 1) (hb : d120178 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d96326, d120178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d96326, d120178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro46772 (p : Pattern) (ha : d96331 p = 1) (hb : d120183 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96225 q = 1) (hb : d120073 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d96225, d120073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46752 q ha hb
    | true =>
      simp only [d96225, d120073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d96226 q = 1) (hb : d120074 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d96226, d120074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96226, d120074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d96227 q = 1) (hb : d120075 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d96227, d120075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d96227, d120075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d96303 q = 1) (hb : d120153 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d96303, d120153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96303, d120153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d96304 q = 1) (hb : d120154 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d96304, d120154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d96304, d120154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d96331 q = 1) (hb : d120183 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d96331, d120183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d96331, d120183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro46773 (p : Pattern) (ha : d96335 p = 1) (hb : d196092 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96314 q = 1) (hb : d196080 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d96314, d196080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46768 q ha hb
    | true =>
      simp only [d96314, d196080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d96315 q = 1) (hb : d196081 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d96315, d196081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96315, d196081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d96225 q = 1) (hb : d120073 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d96225, d120073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46752 q ha hb
    | true =>
      simp only [d96225, d120073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d96226 q = 1) (hb : d120074 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d96226, d120074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96226, d120074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d96316 q = 1) (hb : d196082 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d96316, d196082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d96316, d196082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d96317 q = 1) (hb : d196083 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d96317, d196083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d96317, d196083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d96318 q = 1) (hb : d196084 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d96318, d196084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d96318, d196084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d96335 q = 1) (hb : d196092 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d96335, d196092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d96335, d196092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro46774 (p : Pattern) (ha : d96341 p = 1) (hb : d196098 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96299 q = 1) (hb : d120149 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d96299, d120149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46764 q ha hb
    | true =>
      simp only [d96299, d120149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d96300 q = 1) (hb : d120150 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d96300, d120150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96300, d120150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d96301 q = 1) (hb : d120151 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d96301, d120151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d96301, d120151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d96302 q = 1) (hb : d120152 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d96302, d120152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96302, d120152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d96306 q = 1) (hb : d120156 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d96306, d120156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46765 q ha hb
    | true =>
      simp only [d96306, d120156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d96307 q = 1) (hb : d120157 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d96307, d120157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96307, d120157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d96308 q = 1) (hb : d120158 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d96308, d120158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d96308, d120158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d96320 q = 1) (hb : d196086 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d96320, d196086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46769 q ha hb
    | true =>
      simp only [d96320, d196086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46753 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d96231 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d96321 q = 1) (hb : d196087 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d96321, d196087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d96321, d196087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d96231 q = 1) (hb : d120079 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d96231, d120079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46753 q ha hb
    | true =>
      simp only [d96231, d120079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d96232 q = 1) (hb : d120080 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d96232, d120080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d96232, d120080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d96322 q = 1) (hb : d196088 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d96322, d196088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d96322, d196088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d96323 q = 1) (hb : d196089 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d96323, d196089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d96323, d196089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d96324 q = 1) (hb : d196090 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d96324, d196090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d96324, d196090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d96327 q = 1) (hb : d120179 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d96327, d120179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46771 q ha hb
    | true =>
      simp only [d96327, d120179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h17 (q : Pattern) (ha : d96328 q = 1) (hb : d120180 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d96328, d120180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96328, d120180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d96329 q = 1) (hb : d120181 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d96329, d120181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d96329, d120181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d96330 q = 1) (hb : d120182 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d96330, d120182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96330, d120182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d96332 q = 1) (hb : d120184 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d96332, d120184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46772 q ha hb
    | true =>
      simp only [d96332, d120184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d96333 q = 1) (hb : d120185 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d96333, d120185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96333, d120185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d96334 q = 1) (hb : d120186 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d96334, d120186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d96334, d120186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d96336 q = 1) (hb : d196093 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d96336, d196093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46773 q ha hb
    | true =>
      simp only [d96336, d196093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46755 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d96238 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d96337 q = 1) (hb : d196094 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d96337, d196094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d96337, d196094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d96238 q = 1) (hb : d120086 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d96238, d120086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46755 q ha hb
    | true =>
      simp only [d96238, d120086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d96239 q = 1) (hb : d120087 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d96239, d120087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d96239, d120087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d96338 q = 1) (hb : d196095 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d96338, d196095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d96338, d196095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d96339 q = 1) (hb : d196096 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d96339, d196096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d96339, d196096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d96340 q = 1) (hb : d196097 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d96340, d196097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d96340, d196097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d96341 q = 1) (hb : d196098 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d96341, d196098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d96341, d196098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro46775 (p : Pattern) (ha : d96343 p = 1) (hb : d120195 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96231 q = 1) (hb : d120079 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d96231, d120079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46753 q ha hb
    | true =>
      simp only [d96231, d120079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d96282 q = 1) (hb : d120132 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d96282, d120132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96282, d120132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d96283 q = 1) (hb : d120133 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d96283, d120133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d96283, d120133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d96284 q = 1) (hb : d120134 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d96284, d120134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96284, d120134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d96285 q = 1) (hb : d120135 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d96285, d120135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96285, d120135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d96343 q = 1) (hb : d120195 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d96343, d120195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d96343, d120195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro46776 (p : Pattern) (ha : d96350 p = 1) (hb : d196105 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96336 q = 1) (hb : d196093 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d96336, d196093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46773 q ha hb
    | true =>
      simp only [d96336, d196093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46755 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d96238 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d96337 q = 1) (hb : d196094 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d96337, d196094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d96337, d196094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d96238 q = 1) (hb : d120086 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d96238, d120086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46755 q ha hb
    | true =>
      simp only [d96238, d120086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d96239 q = 1) (hb : d120087 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d96239, d120087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d96239, d120087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d96338 q = 1) (hb : d196095 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d96338, d196095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d96338, d196095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d96348 q = 1) (hb : d196103 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d96348, d196103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96348, d196103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d96349 q = 1) (hb : d196104 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d96349, d196104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96349, d196104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d96350 q = 1) (hb : d196105 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d96350, d196105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96350, d196105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro46777 (p : Pattern) (ha : d52048 p = 1) (hb : d196111 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52048 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d5495 q = 1) (hb : d52044 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5495, d52044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5495, d52044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46766 q ha hb
  have h3 (q : Pattern) (ha : d5451 q = 1) (hb : d51990 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5451, d51990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46766 q ha hb
    | true =>
      simp only [d5451, d51990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d5496 q = 1) (hb : d52045 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5496, d52045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5496, d52045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d5452 q = 1) (hb : d51991 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5452, d51991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5452, d51991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d5497 q = 1) (hb : d52046 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d5497, d52046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5497, d52046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d5498 q = 1) (hb : d52047 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d5498, d52047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d5498, d52047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d66 q = 1) (hb : d51918 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d66, d51918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d66, d51918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2 q ha hb
  have h9 (q : Pattern) (ha : d25 q = 1) (hb : d51877 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25, d51877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2 q ha hb
    | true =>
      simp only [d25, d51877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d67 q = 1) (hb : d51919 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d67, d51919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d67, d51919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d26 q = 1) (hb : d51878 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26, d51878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d26, d51878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h12 (q : Pattern) (ha : d68 q = 1) (hb : d51920 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d68, d51920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d68, d51920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d69 q = 1) (hb : d51921 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d69, d51921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d69, d51921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h14 (q : Pattern) (ha : d21076 q = 1) (hb : d52048 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d21076, d52048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21076, d52048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d52048 q = 1) (hb : d196111 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d196111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d196111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  exact h15 p ha hb
theorem andIntro46778 (p : Pattern) (ha : d96360 p = 1) (hb : d196117 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96356 q = 1) (hb : d196112 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d96356, d196112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46777 q ha hb
    | true =>
      simp only [d96356, d196112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35449 q ha hb
  have h2 (q : Pattern) (ha : d96357 q = 1) (hb : d196113 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d96357, d196113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96357, d196113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d96358 q = 1) (hb : d196114 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d96358, d196114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96358, d196114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d96358 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d96358 q = 1) (hb : d196115 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d196115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d196115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d96254 q = 1) (hb : d120103 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d96254, d120103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35449 q ha hb
    | true =>
      simp only [d96254, d120103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d96255 q = 1) (hb : d120104 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d96255, d120104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96255, d120104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d96256 q = 1) (hb : d120105 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d96256, d120105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96256, d120105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d96256 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d96256 q = 1) (hb : d120106 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d120106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d120106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d96359 q = 1) (hb : d196116 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d96359, d196116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d96359, d196116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d96360 q = 1) (hb : d196117 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d96360, d196117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d96360, d196117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h12 p ha hb
theorem andIntro46779 (p : Pattern) (ha : d96366 p = 1) (hb : d196123 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96361 q = 1) (hb : d196118 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d96361, d196118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46778 q ha hb
    | true =>
      simp only [d96361, d196118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d96362 q = 1) (hb : d196119 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d96362, d196119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96362, d196119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d96259 q = 1) (hb : d120109 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d96259, d120109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46758 q ha hb
    | true =>
      simp only [d96259, d120109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d96260 q = 1) (hb : d120110 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d96260, d120110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96260, d120110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d96363 q = 1) (hb : d196120 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d96363, d196120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d96363, d196120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d96364 q = 1) (hb : d196121 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d96364, d196121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d96364, d196121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d96365 q = 1) (hb : d196122 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d96365, d196122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d96365, d196122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d96366 q = 1) (hb : d196123 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d96366, d196123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d96366, d196123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro46780 (p : Pattern) (ha : d96372 p = 1) (hb : d196129 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96367 q = 1) (hb : d196124 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d96367, d196124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46779 q ha hb
    | true =>
      simp only [d96367, d196124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46759 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d96265 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d96368 q = 1) (hb : d196125 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d96368, d196125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d96368, d196125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d96265 q = 1) (hb : d120115 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d96265, d120115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46759 q ha hb
    | true =>
      simp only [d96265, d120115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d96266 q = 1) (hb : d120116 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d96266, d120116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d96266, d120116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d96369 q = 1) (hb : d196126 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d96369, d196126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d96369, d196126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d96370 q = 1) (hb : d196127 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d96370, d196127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96370, d196127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d96371 q = 1) (hb : d196128 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d96371, d196128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96371, d196128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d96372 q = 1) (hb : d196129 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d96372, d196129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96372, d196129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro46781 (p : Pattern) (ha : d96378 p = 1) (hb : d196135 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96287 q = 1) (hb : d120137 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d96287, d120137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96287, d120137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46762 q ha hb
  have h2 (q : Pattern) (ha : d96288 q = 1) (hb : d120138 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d96288, d120138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d96288, d120138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d96294 q = 1) (hb : d120144 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d96294, d120144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46762 q ha hb
    | true =>
      simp only [d96294, d120144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46763 q ha hb
  have h4 (q : Pattern) (ha : d96295 q = 1) (hb : d120145 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d96295, d120145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d96295, d120145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d96296 q = 1) (hb : d120146 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d96296, d120146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d96296, d120146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d96342 q = 1) (hb : d196099 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d96342, d196099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46770 q ha hb
    | true =>
      simp only [d96342, d196099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46774 q ha hb
  have h7 (q : Pattern) (ha : d96344 q = 1) (hb : d120196 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d96344, d120196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46775 q ha hb
    | true =>
      simp only [d96344, d120196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d96345 q = 1) (hb : d196100 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d96345, d196100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d96345, d196100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d96346 q = 1) (hb : d196101 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d96346, d196101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d96346, d196101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d96347 q = 1) (hb : d196102 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d96347, d196102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d96347, d196102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d96351 q = 1) (hb : d196106 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d96351, d196106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96351, d196106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46776 q ha hb
  have h12 (q : Pattern) (ha : d96352 q = 1) (hb : d196107 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d96352, d196107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d96352, d196107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d96353 q = 1) (hb : d196108 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d96353, d196108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d96353, d196108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d96354 q = 1) (hb : d196109 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d96354, d196109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d96354, d196109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d96355 q = 1) (hb : d196110 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d96355, d196110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d96355, d196110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d96373 q = 1) (hb : d196130 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d96373, d196130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96373, d196130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46780 q ha hb
  have h17 (q : Pattern) (ha : d96374 q = 1) (hb : d196131 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d96374, d196131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d96374, d196131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d96375 q = 1) (hb : d196132 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d96375, d196132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d96375, d196132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d96376 q = 1) (hb : d196133 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d96376, d196133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d96376, d196133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d96377 q = 1) (hb : d196134 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d96377, d196134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d96377, d196134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d96378 q = 1) (hb : d196135 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d96378, d196135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d96378, d196135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro46782 (p : Pattern) (ha : d96384 p = 1) (hb : d196141 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96277 q = 1) (hb : d120127 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d96277, d120127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96277, d120127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46761 q ha hb
  have h2 (q : Pattern) (ha : d96278 q = 1) (hb : d120128 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d96278, d120128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96278, d120128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d96279 q = 1) (hb : d120129 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d96279, d120129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96279, d120129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d96280 q = 1) (hb : d120130 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d96280, d120130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96280, d120130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d96281 q = 1) (hb : d120131 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d96281, d120131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96281, d120131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d96379 q = 1) (hb : d196136 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d96379, d196136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96379, d196136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46781 q ha hb
  have h7 (q : Pattern) (ha : d96380 q = 1) (hb : d196137 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d96380, d196137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96380, d196137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d96381 q = 1) (hb : d196138 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d96381, d196138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96381, d196138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d96382 q = 1) (hb : d196139 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d96382, d196139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96382, d196139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d96383 q = 1) (hb : d196140 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d96383, d196140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96383, d196140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d96384 q = 1) (hb : d196141 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d96384, d196141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d96384, d196141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro46783 (p : Pattern) (ha : d96420 p = 1) (hb : d196079 p = 1) : d197143 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96309 q = 1) (hb : d196074 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d96309, d196074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46767 q ha hb
    | true =>
      simp only [d96309, d196074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35442 q ha hb
  have h2 (q : Pattern) (ha : d96310 q = 1) (hb : d196075 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d96310, d196075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96310, d196075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d96311 q = 1) (hb : d196076 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d96311, d196076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96311, d196076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d96311 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d96311 q = 1) (hb : d196077 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d196077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d196077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d1 q = 1) (hb : d120070 q = 1) : d120070 q = 1 := by
    exact hb
  have h7 (q : Pattern) (ha : d96419 q = 1) (hb : d196078 q = 1) : d197142 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d96419, d196078, d197142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d96419, d196078, d197142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d96420 q = 1) (hb : d196079 q = 1) : d197143 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d96420, d196079, d197143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d96420, d196079, d197143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro46784 (p : Pattern) (ha : d195386 p = 1) (hb : d196085 p = 1) : d197149 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96421 q = 1) (hb : d196080 q = 1) : d197144 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d96421, d196080, d197144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46783 q ha hb
    | true =>
      simp only [d96421, d196080, d197144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d96422 q = 1) (hb : d196081 q = 1) : d197145 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d96422, d196081, d197145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96422, d196081, d197145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1 q = 1) (hb : d120074 q = 1) : d120074 q = 1 := by
    exact hb
  have h4 (q : Pattern) (ha : d195383 q = 1) (hb : d196082 q = 1) : d197146 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d195383, d196082, d197146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d195383, d196082, d197146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d195384 q = 1) (hb : d196083 q = 1) : d197147 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d195384, d196083, d197147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d195384, d196083, d197147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d195385 q = 1) (hb : d196084 q = 1) : d197148 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d195385, d196084, d197148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d195385, d196084, d197148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d195386 q = 1) (hb : d196085 q = 1) : d197149 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d195386, d196085, d197149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195386, d196085, d197149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro46785 (p : Pattern) (ha : d195392 p = 1) (hb : d196146 p = 1) : d197155 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d120078 q = 1) : d120078 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d195387 q = 1) (hb : d196086 q = 1) : d197150 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195387, d196086, d197150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46784 q ha hb
    | true =>
      simp only [d195387, d196086, d197150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d195388 q = 1) (hb : d196142 q = 1) : d197151 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d195388, d196142, d197151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195388, d196142, d197151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d195389 q = 1) (hb : d196143 q = 1) : d197152 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d195389, d196143, d197152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d195389, d196143, d197152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d195390 q = 1) (hb : d196144 q = 1) : d197153 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d195390, d196144, d197153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195390, d196144, d197153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d195391 q = 1) (hb : d196145 q = 1) : d197154 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d195391, d196145, d197154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195391, d196145, d197154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d195392 q = 1) (hb : d196146 q = 1) : d197155 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d195392, d196146, d197155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195392, d196146, d197155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro46786 (p : Pattern) (ha : d195395 p = 1) (hb : d196092 p = 1) : d197158 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96421 q = 1) (hb : d196080 q = 1) : d197144 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d96421, d196080, d197144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46783 q ha hb
    | true =>
      simp only [d96421, d196080, d197144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d96422 q = 1) (hb : d196081 q = 1) : d197145 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d96422, d196081, d197145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96422, d196081, d197145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1 q = 1) (hb : d120074 q = 1) : d120074 q = 1 := by
    exact hb
  have h4 (q : Pattern) (ha : d195383 q = 1) (hb : d196082 q = 1) : d197146 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d195383, d196082, d197146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d195383, d196082, d197146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d195384 q = 1) (hb : d196083 q = 1) : d197147 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d195384, d196083, d197147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d195384, d196083, d197147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d195385 q = 1) (hb : d196084 q = 1) : d197148 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d195385, d196084, d197148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d195385, d196084, d197148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d195395 q = 1) (hb : d196092 q = 1) : d197158 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d195395, d196092, d197158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d195395, d196092, d197158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro46787 (p : Pattern) (ha : d195401 p = 1) (hb : d196153 p = 1) : d197164 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d120078 q = 1) : d120078 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d195387 q = 1) (hb : d196086 q = 1) : d197150 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195387, d196086, d197150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46784 q ha hb
    | true =>
      simp only [d195387, d196086, d197150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d195388 q = 1) (hb : d196142 q = 1) : d197151 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d195388, d196142, d197151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195388, d196142, d197151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d195389 q = 1) (hb : d196143 q = 1) : d197152 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d195389, d196143, d197152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d195389, d196143, d197152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d195390 q = 1) (hb : d196144 q = 1) : d197153 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d195390, d196144, d197153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195390, d196144, d197153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d195391 q = 1) (hb : d196145 q = 1) : d197154 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d195391, d196145, d197154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195391, d196145, d197154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1 q = 1) (hb : d120085 q = 1) : d120085 q = 1 := by
    exact hb
  have h8 (q : Pattern) (ha : d195396 q = 1) (hb : d196093 q = 1) : d197159 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195396, d196093, d197159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46786 q ha hb
    | true =>
      simp only [d195396, d196093, d197159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d195397 q = 1) (hb : d196149 q = 1) : d197160 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d195397, d196149, d197160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195397, d196149, d197160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d195398 q = 1) (hb : d196150 q = 1) : d197161 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d195398, d196150, d197161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d195398, d196150, d197161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d195399 q = 1) (hb : d196151 q = 1) : d197162 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d195399, d196151, d197162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195399, d196151, d197162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d195400 q = 1) (hb : d196152 q = 1) : d197163 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d195400, d196152, d197163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195400, d196152, d197163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d195401 q = 1) (hb : d196153 q = 1) : d197164 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d195401, d196153, d197164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d195401, d196153, d197164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro46788 (p : Pattern) (ha : d195386 p = 1) (hb : d196187 p = 1) : d197189 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96421 q = 1) (hb : d196080 q = 1) : d197144 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d96421, d196080, d197144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46783 q ha hb
    | true =>
      simp only [d96421, d196080, d197144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d96422 q = 1) (hb : d196081 q = 1) : d197145 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d96422, d196081, d197145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96422, d196081, d197145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d195383 q = 1) (hb : d196184 q = 1) : d197186 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d195383, d196184, d197186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d195383, d196184, d197186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d195384 q = 1) (hb : d196185 q = 1) : d197187 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d195384, d196185, d197187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d195384, d196185, d197187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d195385 q = 1) (hb : d196186 q = 1) : d197188 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d195385, d196186, d197188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d195385, d196186, d197188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d195386 q = 1) (hb : d196187 q = 1) : d197189 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d195386, d196187, d197189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195386, d196187, d197189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro46789 (p : Pattern) (ha : d195406 p = 1) (hb : d196158 p = 1) : d197169 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96421 q = 1) (hb : d196080 q = 1) : d197144 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d96421, d196080, d197144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46783 q ha hb
    | true =>
      simp only [d96421, d196080, d197144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d96422 q = 1) (hb : d196081 q = 1) : d197145 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d96422, d196081, d197145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96422, d196081, d197145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1 q = 1) (hb : d120074 q = 1) : d120074 q = 1 := by
    exact hb
  have h4 (q : Pattern) (ha : d195383 q = 1) (hb : d196082 q = 1) : d197146 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d195383, d196082, d197146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d195383, d196082, d197146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d195384 q = 1) (hb : d196083 q = 1) : d197147 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d195384, d196083, d197147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d195384, d196083, d197147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d195405 q = 1) (hb : d196157 q = 1) : d197168 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d195405, d196157, d197168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195405, d196157, d197168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d195406 q = 1) (hb : d196158 q = 1) : d197169 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d195406, d196158, d197169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195406, d196158, d197169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro46790 (p : Pattern) (ha : d195413 p = 1) (hb : d196165 p = 1) : d197176 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96421 q = 1) (hb : d196080 q = 1) : d197144 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d96421, d196080, d197144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46783 q ha hb
    | true =>
      simp only [d96421, d196080, d197144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d96422 q = 1) (hb : d196081 q = 1) : d197145 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d96422, d196081, d197145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96422, d196081, d197145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1 q = 1) (hb : d120074 q = 1) : d120074 q = 1 := by
    exact hb
  have h4 (q : Pattern) (ha : d195383 q = 1) (hb : d196082 q = 1) : d197146 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d195383, d196082, d197146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d195383, d196082, d197146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d195411 q = 1) (hb : d196163 q = 1) : d197174 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d195411, d196163, d197174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195411, d196163, d197174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d195412 q = 1) (hb : d196164 q = 1) : d197175 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d195412, d196164, d197175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d195412, d196164, d197175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d195413 q = 1) (hb : d196165 q = 1) : d197176 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d195413, d196165, d197176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195413, d196165, d197176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro46791 (p : Pattern) (ha : d21188 p = 1) (hb : d52117 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d313 q = 1) (hb : d52112 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d313, d52112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41 q ha hb
    | true =>
      simp only [d313, d52112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d314 q = 1) (hb : d52113 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d314, d52113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d314, d52113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d9452 q = 1) (hb : d51984 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d9452, d51984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35483 q ha hb
    | true =>
      simp only [d9452, d51984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d9453 q = 1) (hb : d51985 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d9453, d51985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9453, d51985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d9464 q = 1) (hb : d52114 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d9464, d52114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9464, d52114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d51986 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d9465 q = 1) (hb : d52115 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d9465, d52115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9465, d52115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d9466 q = 1) (hb : d52116 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d9466, d52116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d9466, d52116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d51988 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d21188 q = 1) (hb : d52117 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d21188, d52117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d21188, d52117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro46792 (p : Pattern) (ha : d52122 p = 1) (hb : d196169 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52122 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d21189 q = 1) (hb : d52118 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21189, d52118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46791 q ha hb
    | true =>
      simp only [d21189, d52118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21190 q = 1) (hb : d52119 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21190, d52119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21190, d52119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d21191 q = 1) (hb : d52120 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d21191, d52120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d21191, d52120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21192 q = 1) (hb : d52121 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d21192, d52121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21192, d52121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d5451 q = 1) (hb : d51990 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5451, d51990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46766 q ha hb
    | true =>
      simp only [d5451, d51990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d5452 q = 1) (hb : d51991 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5452, d51991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d5452, d51991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d5453 q = 1) (hb : d51992 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d5453, d51992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5453, d51992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d5454 q = 1) (hb : d51993 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d5454, d51993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d5454, d51993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d21193 q = 1) (hb : d52122 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d21193, d52122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21193, d52122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d52122 q = 1) (hb : d196169 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d196169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d196169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro46793 (p : Pattern) (ha : d112929 p = 1) (hb : d196073 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112929 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d5451 q = 1) (hb : d101015 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5451, d101015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46070 q ha hb
    | true =>
      simp only [d5451, d101015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d5452 q = 1) (hb : d101017 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5452, d101017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5452, d101017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d5453 q = 1) (hb : d112927 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d5453, d112927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5453, d112927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d5454 q = 1) (hb : d112928 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d5454, d112928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5454, d112928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d25 q = 1) (hb : d51877 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25, d51877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2 q ha hb
    | true =>
      simp only [d25, d51877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d26 q = 1) (hb : d51878 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26, d51878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d26, d51878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d27 q = 1) (hb : d51879 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d27, d51879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d27, d51879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d28 q = 1) (hb : d51880 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d28, d51880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d28, d51880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d20995 q = 1) (hb : d112929 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d20995, d112929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20995, d112929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d112929 q = 1) (hb : d196073 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d196073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d196073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro46794 (p : Pattern) (ha : d195421 p = 1) (hb : d196175 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d195417 q = 1) (hb : d196170 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d195417, d196170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46792 q ha hb
    | true =>
      simp only [d195417, d196170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46793 q ha hb
  have h2 (q : Pattern) (ha : d195418 q = 1) (hb : d196171 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d195418, d196171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195418, d196171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d195419 q = 1) (hb : d196172 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d195419, d196172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195419, d196172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d195419 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d195419 q = 1) (hb : d196173 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d196173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d196173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d96309 q = 1) (hb : d196074 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d96309, d196074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46767 q ha hb
    | true =>
      simp only [d96309, d196074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35442 q ha hb
  have h7 (q : Pattern) (ha : d96310 q = 1) (hb : d196075 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d96310, d196075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96310, d196075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d96311 q = 1) (hb : d196076 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d96311, d196076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96311, d196076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d96311 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d96311 q = 1) (hb : d196077 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d196077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d196077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d195420 q = 1) (hb : d196174 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d195420, d196174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d195420, d196174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d195421 q = 1) (hb : d196175 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d195421, d196175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d195421, d196175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h12 p ha hb
theorem andIntro46795 (p : Pattern) (ha : d195427 p = 1) (hb : d196181 p = 1) : d197183 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d195422 q = 1) (hb : d196176 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d195422, d196176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46794 q ha hb
    | true =>
      simp only [d195422, d196176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d195423 q = 1) (hb : d196177 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d195423, d196177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195423, d196177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d96421 q = 1) (hb : d196080 q = 1) : d197144 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d96421, d196080, d197144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46783 q ha hb
    | true =>
      simp only [d96421, d196080, d197144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d96422 q = 1) (hb : d196081 q = 1) : d197145 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d96422, d196081, d197145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96422, d196081, d197145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d195424 q = 1) (hb : d196178 q = 1) : d197180 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d195424, d196178, d197180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d195424, d196178, d197180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d195425 q = 1) (hb : d196179 q = 1) : d197181 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d195425, d196179, d197181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d195425, d196179, d197181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d195426 q = 1) (hb : d196180 q = 1) : d197182 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d195426, d196180, d197182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d195426, d196180, d197182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d195427 q = 1) (hb : d196181 q = 1) : d197183 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d195427, d196181, d197183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195427, d196181, d197183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro46796 (p : Pattern) (ha : d195434 p = 1) (hb : d196193 p = 1) : d197195 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d120148 q = 1) : d120148 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d195407 q = 1) (hb : d196159 q = 1) : d197170 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195407, d196159, d197170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46789 q ha hb
    | true =>
      simp only [d195407, d196159, d197170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d195408 q = 1) (hb : d196160 q = 1) : d197171 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d195408, d196160, d197171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195408, d196160, d197171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d195409 q = 1) (hb : d196161 q = 1) : d197172 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d195409, d196161, d197172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d195409, d196161, d197172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d195410 q = 1) (hb : d196162 q = 1) : d197173 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d195410, d196162, d197173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195410, d196162, d197173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1 q = 1) (hb : d120155 q = 1) : d120155 q = 1 := by
    exact hb
  have h7 (q : Pattern) (ha : d195414 q = 1) (hb : d196166 q = 1) : d197177 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195414, d196166, d197177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46790 q ha hb
    | true =>
      simp only [d195414, d196166, d197177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d195415 q = 1) (hb : d196167 q = 1) : d197178 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d195415, d196167, d197178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195415, d196167, d197178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d195416 q = 1) (hb : d196168 q = 1) : d197179 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d195416, d196168, d197179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d195416, d196168, d197179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d195428 q = 1) (hb : d196182 q = 1) : d197184 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195428, d196182, d197184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46795 q ha hb
    | true =>
      simp only [d195428, d196182, d197184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46784 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d195387 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d195429 q = 1) (hb : d196183 q = 1) : d197185 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d195429, d196183, d197185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d195429, d196183, d197185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d195387 q = 1) (hb : d196188 q = 1) : d197190 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195387, d196188, d197190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46788 q ha hb
    | true =>
      simp only [d195387, d196188, d197190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d195430 q = 1) (hb : d196189 q = 1) : d197191 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d195430, d196189, d197191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d195430, d196189, d197191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d195431 q = 1) (hb : d196190 q = 1) : d197192 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d195431, d196190, d197192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d195431, d196190, d197192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d195432 q = 1) (hb : d196191 q = 1) : d197193 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d195432, d196191, d197193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d195432, d196191, d197193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d195433 q = 1) (hb : d196192 q = 1) : d197194 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d195433, d196192, d197194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d195433, d196192, d197194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d195434 q = 1) (hb : d196193 q = 1) : d197195 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d195434, d196193, d197195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195434, d196193, d197195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro46797 (p : Pattern) (ha : d195395 p = 1) (hb : d196206 p = 1) : d197208 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96421 q = 1) (hb : d196080 q = 1) : d197144 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d96421, d196080, d197144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46783 q ha hb
    | true =>
      simp only [d96421, d196080, d197144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d96422 q = 1) (hb : d196081 q = 1) : d197145 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d96422, d196081, d197145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96422, d196081, d197145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d195383 q = 1) (hb : d196184 q = 1) : d197186 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d195383, d196184, d197186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d195383, d196184, d197186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d195384 q = 1) (hb : d196185 q = 1) : d197187 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d195384, d196185, d197187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d195384, d196185, d197187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d195385 q = 1) (hb : d196186 q = 1) : d197188 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d195385, d196186, d197188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d195385, d196186, d197188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d195395 q = 1) (hb : d196206 q = 1) : d197208 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d195395, d196206, d197208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d195395, d196206, d197208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro46798 (p : Pattern) (ha : d195435 p = 1) (hb : d196194 p = 1) : d197196 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96421 q = 1) (hb : d196080 q = 1) : d197144 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d96421, d196080, d197144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46783 q ha hb
    | true =>
      simp only [d96421, d196080, d197144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d96422 q = 1) (hb : d196081 q = 1) : d197145 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d96422, d196081, d197145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96422, d196081, d197145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1 q = 1) (hb : d120074 q = 1) : d120074 q = 1 := by
    exact hb
  have h4 (q : Pattern) (ha : d195383 q = 1) (hb : d196082 q = 1) : d197146 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d195383, d196082, d197146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d195383, d196082, d197146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d195384 q = 1) (hb : d196083 q = 1) : d197147 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d195384, d196083, d197147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d195384, d196083, d197147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d195405 q = 1) (hb : d196157 q = 1) : d197168 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d195405, d196157, d197168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195405, d196157, d197168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d195435 q = 1) (hb : d196194 q = 1) : d197196 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d195435, d196194, d197196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d195435, d196194, d197196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro46799 (p : Pattern) (ha : d195440 p = 1) (hb : d196199 p = 1) : d197201 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96421 q = 1) (hb : d196080 q = 1) : d197144 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d96421, d196080, d197144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46783 q ha hb
    | true =>
      simp only [d96421, d196080, d197144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d96422 q = 1) (hb : d196081 q = 1) : d197145 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d96422, d196081, d197145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96422, d196081, d197145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1 q = 1) (hb : d120074 q = 1) : d120074 q = 1 := by
    exact hb
  have h4 (q : Pattern) (ha : d195383 q = 1) (hb : d196082 q = 1) : d197146 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d195383, d196082, d197146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d195383, d196082, d197146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d195411 q = 1) (hb : d196163 q = 1) : d197174 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d195411, d196163, d197174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195411, d196163, d197174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d195412 q = 1) (hb : d196164 q = 1) : d197175 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d195412, d196164, d197175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d195412, d196164, d197175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d195440 q = 1) (hb : d196199 q = 1) : d197201 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d195440, d196199, d197201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d195440, d196199, d197201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro46800 (p : Pattern) (ha : d195444 p = 1) (hb : d196203 p = 1) : d197205 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d195422 q = 1) (hb : d196176 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d195422, d196176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46794 q ha hb
    | true =>
      simp only [d195422, d196176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d195423 q = 1) (hb : d196177 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d195423, d196177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195423, d196177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d96421 q = 1) (hb : d196080 q = 1) : d197144 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d96421, d196080, d197144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46783 q ha hb
    | true =>
      simp only [d96421, d196080, d197144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d96422 q = 1) (hb : d196081 q = 1) : d197145 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d96422, d196081, d197145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96422, d196081, d197145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d195424 q = 1) (hb : d196178 q = 1) : d197180 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d195424, d196178, d197180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d195424, d196178, d197180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d195425 q = 1) (hb : d196179 q = 1) : d197181 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d195425, d196179, d197181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d195425, d196179, d197181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d195426 q = 1) (hb : d196180 q = 1) : d197182 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d195426, d196180, d197182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d195426, d196180, d197182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d195444 q = 1) (hb : d196203 q = 1) : d197205 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d195444, d196203, d197205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d195444, d196203, d197205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro46801 (p : Pattern) (ha : d195451 p = 1) (hb : d196212 p = 1) : d197214 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d120148 q = 1) : d120148 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d195407 q = 1) (hb : d196159 q = 1) : d197170 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195407, d196159, d197170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46789 q ha hb
    | true =>
      simp only [d195407, d196159, d197170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d195408 q = 1) (hb : d196160 q = 1) : d197171 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d195408, d196160, d197171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195408, d196160, d197171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d195409 q = 1) (hb : d196161 q = 1) : d197172 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d195409, d196161, d197172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d195409, d196161, d197172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d195410 q = 1) (hb : d196162 q = 1) : d197173 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d195410, d196162, d197173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195410, d196162, d197173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1 q = 1) (hb : d120155 q = 1) : d120155 q = 1 := by
    exact hb
  have h7 (q : Pattern) (ha : d195414 q = 1) (hb : d196166 q = 1) : d197177 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195414, d196166, d197177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46790 q ha hb
    | true =>
      simp only [d195414, d196166, d197177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d195415 q = 1) (hb : d196167 q = 1) : d197178 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d195415, d196167, d197178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195415, d196167, d197178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d195416 q = 1) (hb : d196168 q = 1) : d197179 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d195416, d196168, d197179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d195416, d196168, d197179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d195428 q = 1) (hb : d196182 q = 1) : d197184 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195428, d196182, d197184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46795 q ha hb
    | true =>
      simp only [d195428, d196182, d197184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46784 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d195387 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d195429 q = 1) (hb : d196183 q = 1) : d197185 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d195429, d196183, d197185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d195429, d196183, d197185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d195387 q = 1) (hb : d196188 q = 1) : d197190 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195387, d196188, d197190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46788 q ha hb
    | true =>
      simp only [d195387, d196188, d197190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d195430 q = 1) (hb : d196189 q = 1) : d197191 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d195430, d196189, d197191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d195430, d196189, d197191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d195431 q = 1) (hb : d196190 q = 1) : d197192 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d195431, d196190, d197192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d195431, d196190, d197192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d195432 q = 1) (hb : d196191 q = 1) : d197193 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d195432, d196191, d197193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d195432, d196191, d197193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d195433 q = 1) (hb : d196192 q = 1) : d197194 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d195433, d196192, d197194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d195433, d196192, d197194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d1 q = 1) (hb : d120178 q = 1) : d120178 q = 1 := by
    exact hb
  have h19 (q : Pattern) (ha : d195436 q = 1) (hb : d196195 q = 1) : d197197 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195436, d196195, d197197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46798 q ha hb
    | true =>
      simp only [d195436, d196195, d197197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d195437 q = 1) (hb : d196196 q = 1) : d197198 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d195437, d196196, d197198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195437, d196196, d197198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d195438 q = 1) (hb : d196197 q = 1) : d197199 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d195438, d196197, d197199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d195438, d196197, d197199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d195439 q = 1) (hb : d196198 q = 1) : d197200 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d195439, d196198, d197200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195439, d196198, d197200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d1 q = 1) (hb : d120183 q = 1) : d120183 q = 1 := by
    exact hb
  have h24 (q : Pattern) (ha : d195441 q = 1) (hb : d196200 q = 1) : d197202 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195441, d196200, d197202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46799 q ha hb
    | true =>
      simp only [d195441, d196200, d197202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d195442 q = 1) (hb : d196201 q = 1) : d197203 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d195442, d196201, d197203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195442, d196201, d197203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
  have h26 (q : Pattern) (ha : d195443 q = 1) (hb : d196202 q = 1) : d197204 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d195443, d196202, d197204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d195443, d196202, d197204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d195445 q = 1) (hb : d196204 q = 1) : d197206 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195445, d196204, d197206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46800 q ha hb
    | true =>
      simp only [d195445, d196204, d197206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46786 q ha hb
  have h28 (q : Pattern) (ha : d0 q = 1) (hb : d195396 q = 1) : d0 q = 1 := by
    exact ha
  have h29 (q : Pattern) (ha : d195446 q = 1) (hb : d196205 q = 1) : d197207 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d195446, d196205, d197207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
    | true =>
      simp only [d195446, d196205, d197207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q hb ha
  have h30 (q : Pattern) (ha : d195396 q = 1) (hb : d196207 q = 1) : d197209 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195396, d196207, d197209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46797 q ha hb
    | true =>
      simp only [d195396, d196207, d197209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h31 (q : Pattern) (ha : d195447 q = 1) (hb : d196208 q = 1) : d197210 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d195447, d196208, d197210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
    | true =>
      simp only [d195447, d196208, d197210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h32 (q : Pattern) (ha : d195448 q = 1) (hb : d196209 q = 1) : d197211 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d195448, d196209, d197211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
    | true =>
      simp only [d195448, d196209, d197211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
  have h33 (q : Pattern) (ha : d195449 q = 1) (hb : d196210 q = 1) : d197212 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d195449, d196210, d197212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d195449, d196210, d197212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h32 q ha hb
  have h34 (q : Pattern) (ha : d195450 q = 1) (hb : d196211 q = 1) : d197213 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d195450, d196211, d197213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d195450, d196211, d197213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h33 q ha hb
  have h35 (q : Pattern) (ha : d195451 q = 1) (hb : d196212 q = 1) : d197214 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d195451, d196212, d197214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d195451, d196212, d197214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h34 q ha hb
  exact h35 p ha hb
theorem andIntro46802 (p : Pattern) (ha : d195453 p = 1) (hb : d196214 p = 1) : d197216 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d120078 q = 1) : d120078 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d195387 q = 1) (hb : d196086 q = 1) : d197150 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195387, d196086, d197150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46784 q ha hb
    | true =>
      simp only [d195387, d196086, d197150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d195388 q = 1) (hb : d196142 q = 1) : d197151 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d195388, d196142, d197151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195388, d196142, d197151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d195389 q = 1) (hb : d196143 q = 1) : d197152 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d195389, d196143, d197152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d195389, d196143, d197152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d195390 q = 1) (hb : d196144 q = 1) : d197153 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d195390, d196144, d197153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195390, d196144, d197153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d195391 q = 1) (hb : d196145 q = 1) : d197154 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d195391, d196145, d197154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195391, d196145, d197154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1 q = 1) (hb : d120135 q = 1) : d120135 q = 1 := by
    exact hb
  have h8 (q : Pattern) (ha : d195453 q = 1) (hb : d196214 q = 1) : d197216 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d195453, d196214, d197216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d195453, d196214, d197216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro46803 (p : Pattern) (ha : d195460 p = 1) (hb : d196221 p = 1) : d197223 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d195445 q = 1) (hb : d196204 q = 1) : d197206 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195445, d196204, d197206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46800 q ha hb
    | true =>
      simp only [d195445, d196204, d197206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46786 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d195396 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d195446 q = 1) (hb : d196205 q = 1) : d197207 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d195446, d196205, d197207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d195446, d196205, d197207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d195396 q = 1) (hb : d196207 q = 1) : d197209 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195396, d196207, d197209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46797 q ha hb
    | true =>
      simp only [d195396, d196207, d197209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d195447 q = 1) (hb : d196208 q = 1) : d197210 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d195447, d196208, d197210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d195447, d196208, d197210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d195448 q = 1) (hb : d196209 q = 1) : d197211 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d195448, d196209, d197211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d195448, d196209, d197211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d195458 q = 1) (hb : d196219 q = 1) : d197221 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d195458, d196219, d197221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195458, d196219, d197221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d195459 q = 1) (hb : d196220 q = 1) : d197222 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d195459, d196220, d197222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195459, d196220, d197222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d195460 q = 1) (hb : d196221 q = 1) : d197223 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d195460, d196221, d197223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195460, d196221, d197223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro46804 (p : Pattern) (ha : d96492 p = 1) (hb : d196117 p = 1) : d197230 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96356 q = 1) (hb : d196112 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d96356, d196112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46777 q ha hb
    | true =>
      simp only [d96356, d196112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35449 q ha hb
  have h2 (q : Pattern) (ha : d96357 q = 1) (hb : d196113 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d96357, d196113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96357, d196113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d96358 q = 1) (hb : d196114 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d96358, d196114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96358, d196114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d96358 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d96358 q = 1) (hb : d196115 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d196115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d196115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d1 q = 1) (hb : d120106 q = 1) : d120106 q = 1 := by
    exact hb
  have h7 (q : Pattern) (ha : d96491 q = 1) (hb : d196116 q = 1) : d197229 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d96491, d196116, d197229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d96491, d196116, d197229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d96492 q = 1) (hb : d196117 q = 1) : d197230 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d96492, d196117, d197230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d96492, d196117, d197230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro46805 (p : Pattern) (ha : d52182 p = 1) (hb : d196227 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52182 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d21314 q = 1) (hb : d52178 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21314, d52178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d21314, d52178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46791 q ha hb
  have h3 (q : Pattern) (ha : d21189 q = 1) (hb : d52118 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21189, d52118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46791 q ha hb
    | true =>
      simp only [d21189, d52118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d21315 q = 1) (hb : d52179 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21315, d52179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21315, d52179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21190 q = 1) (hb : d52119 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21190, d52119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21190, d52119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d21316 q = 1) (hb : d52180 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d21316, d52180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21316, d52180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d21317 q = 1) (hb : d52181 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d21317, d52181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21317, d52181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d5495 q = 1) (hb : d52044 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5495, d52044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5495, d52044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46766 q ha hb
  have h9 (q : Pattern) (ha : d5451 q = 1) (hb : d51990 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5451, d51990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46766 q ha hb
    | true =>
      simp only [d5451, d51990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d5496 q = 1) (hb : d52045 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5496, d52045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d5496, d52045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d5452 q = 1) (hb : d51991 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5452, d51991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d5452, d51991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h12 (q : Pattern) (ha : d5497 q = 1) (hb : d52046 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d5497, d52046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d5497, d52046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d5498 q = 1) (hb : d52047 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d5498, d52047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d5498, d52047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h14 (q : Pattern) (ha : d21318 q = 1) (hb : d52182 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d21318, d52182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21318, d52182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d52182 q = 1) (hb : d196227 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d196227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d196227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  exact h15 p ha hb
theorem andIntro46806 (p : Pattern) (ha : d113011 p = 1) (hb : d196111 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d113011 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d5495 q = 1) (hb : d113007 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5495, d113007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5495, d113007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46070 q ha hb
  have h3 (q : Pattern) (ha : d5451 q = 1) (hb : d101015 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5451, d101015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46070 q ha hb
    | true =>
      simp only [d5451, d101015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d5496 q = 1) (hb : d113008 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5496, d113008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5496, d113008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d5452 q = 1) (hb : d101017 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5452, d101017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5452, d101017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d5497 q = 1) (hb : d113009 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d5497, d113009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5497, d113009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d5498 q = 1) (hb : d113010 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d5498, d113010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d5498, d113010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d66 q = 1) (hb : d51918 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d66, d51918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d66, d51918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2 q ha hb
  have h9 (q : Pattern) (ha : d25 q = 1) (hb : d51877 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25, d51877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2 q ha hb
    | true =>
      simp only [d25, d51877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d67 q = 1) (hb : d51919 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d67, d51919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d67, d51919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d26 q = 1) (hb : d51878 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26, d51878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d26, d51878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h12 (q : Pattern) (ha : d68 q = 1) (hb : d51920 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d68, d51920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d68, d51920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d69 q = 1) (hb : d51921 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d69, d51921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d69, d51921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h14 (q : Pattern) (ha : d21076 q = 1) (hb : d113011 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d21076, d113011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21076, d113011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d113011 q = 1) (hb : d196111 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d196111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d196111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  exact h15 p ha hb
theorem andIntro46807 (p : Pattern) (ha : d195470 p = 1) (hb : d196233 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d195466 q = 1) (hb : d196228 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d195466, d196228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46805 q ha hb
    | true =>
      simp only [d195466, d196228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46806 q ha hb
  have h2 (q : Pattern) (ha : d195467 q = 1) (hb : d196229 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d195467, d196229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195467, d196229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d195468 q = 1) (hb : d196230 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d195468, d196230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195468, d196230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d195468 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d195468 q = 1) (hb : d196231 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d196231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d196231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d96356 q = 1) (hb : d196112 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d96356, d196112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46777 q ha hb
    | true =>
      simp only [d96356, d196112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35449 q ha hb
  have h7 (q : Pattern) (ha : d96357 q = 1) (hb : d196113 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d96357, d196113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96357, d196113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d96358 q = 1) (hb : d196114 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d96358, d196114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96358, d196114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d96358 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d96358 q = 1) (hb : d196115 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d196115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d196115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d195469 q = 1) (hb : d196232 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d195469, d196232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d195469, d196232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d195470 q = 1) (hb : d196233 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d195470, d196233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d195470, d196233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h12 p ha hb
theorem andIntro46808 (p : Pattern) (ha : d195476 p = 1) (hb : d196239 p = 1) : d197236 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d195471 q = 1) (hb : d196234 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d195471, d196234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46807 q ha hb
    | true =>
      simp only [d195471, d196234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d195472 q = 1) (hb : d196235 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d195472, d196235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195472, d196235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d96493 q = 1) (hb : d196118 q = 1) : d197231 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d96493, d196118, d197231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46804 q ha hb
    | true =>
      simp only [d96493, d196118, d197231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d96494 q = 1) (hb : d196119 q = 1) : d197232 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d96494, d196119, d197232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96494, d196119, d197232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d195473 q = 1) (hb : d196236 q = 1) : d197233 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d195473, d196236, d197233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d195473, d196236, d197233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d195474 q = 1) (hb : d196237 q = 1) : d197234 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d195474, d196237, d197234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d195474, d196237, d197234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d195475 q = 1) (hb : d196238 q = 1) : d197235 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d195475, d196238, d197235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d195475, d196238, d197235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d195476 q = 1) (hb : d196239 q = 1) : d197236 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d195476, d196239, d197236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d195476, d196239, d197236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro46809 (p : Pattern) (ha : d195480 p = 1) (hb : d196123 p = 1) : d197240 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96493 q = 1) (hb : d196118 q = 1) : d197231 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d96493, d196118, d197231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46804 q ha hb
    | true =>
      simp only [d96493, d196118, d197231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d96494 q = 1) (hb : d196119 q = 1) : d197232 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d96494, d196119, d197232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96494, d196119, d197232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1 q = 1) (hb : d120110 q = 1) : d120110 q = 1 := by
    exact hb
  have h4 (q : Pattern) (ha : d195477 q = 1) (hb : d196120 q = 1) : d197237 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d195477, d196120, d197237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d195477, d196120, d197237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d195478 q = 1) (hb : d196121 q = 1) : d197238 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d195478, d196121, d197238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d195478, d196121, d197238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d195479 q = 1) (hb : d196122 q = 1) : d197239 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d195479, d196122, d197239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d195479, d196122, d197239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d195480 q = 1) (hb : d196123 q = 1) : d197240 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d195480, d196123, d197240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d195480, d196123, d197240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro46810 (p : Pattern) (ha : d195480 p = 1) (hb : d196245 p = 1) : d197246 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96493 q = 1) (hb : d196118 q = 1) : d197231 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d96493, d196118, d197231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46804 q ha hb
    | true =>
      simp only [d96493, d196118, d197231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d96494 q = 1) (hb : d196119 q = 1) : d197232 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d96494, d196119, d197232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96494, d196119, d197232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d195477 q = 1) (hb : d196242 q = 1) : d197243 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d195477, d196242, d197243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d195477, d196242, d197243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d195478 q = 1) (hb : d196243 q = 1) : d197244 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d195478, d196243, d197244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d195478, d196243, d197244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d195479 q = 1) (hb : d196244 q = 1) : d197245 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d195479, d196244, d197245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d195479, d196244, d197245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d195480 q = 1) (hb : d196245 q = 1) : d197246 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d195480, d196245, d197246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d195480, d196245, d197246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro46811 (p : Pattern) (ha : d195488 p = 1) (hb : d196251 p = 1) : d197252 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d195481 q = 1) (hb : d196240 q = 1) : d197241 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195481, d196240, d197241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46808 q ha hb
    | true =>
      simp only [d195481, d196240, d197241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46809 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d195482 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d195483 q = 1) (hb : d196241 q = 1) : d197242 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d195483, d196241, d197242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d195483, d196241, d197242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d195482 q = 1) (hb : d196246 q = 1) : d197247 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195482, d196246, d197247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46810 q ha hb
    | true =>
      simp only [d195482, d196246, d197247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d195484 q = 1) (hb : d196247 q = 1) : d197248 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d195484, d196247, d197248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d195484, d196247, d197248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d195485 q = 1) (hb : d196248 q = 1) : d197249 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d195485, d196248, d197249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d195485, d196248, d197249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d195486 q = 1) (hb : d196249 q = 1) : d197250 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d195486, d196249, d197250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195486, d196249, d197250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d195487 q = 1) (hb : d196250 q = 1) : d197251 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d195487, d196250, d197251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195487, d196250, d197251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d195488 q = 1) (hb : d196251 q = 1) : d197252 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d195488, d196251, d197252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195488, d196251, d197252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro46812 (p : Pattern) (ha : d195494 p = 1) (hb : d196257 p = 1) : d197258 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d195393 q = 1) (hb : d196147 q = 1) : d197156 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d195393, d196147, d197156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195393, d196147, d197156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46785 q ha hb
  have h2 (q : Pattern) (ha : d195394 q = 1) (hb : d196148 q = 1) : d197157 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d195394, d196148, d197157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d195394, d196148, d197157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d195402 q = 1) (hb : d196154 q = 1) : d197165 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d195402, d196154, d197165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46785 q ha hb
    | true =>
      simp only [d195402, d196154, d197165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46787 q ha hb
  have h4 (q : Pattern) (ha : d195403 q = 1) (hb : d196155 q = 1) : d197166 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d195403, d196155, d197166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d195403, d196155, d197166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d195404 q = 1) (hb : d196156 q = 1) : d197167 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d195404, d196156, d197167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d195404, d196156, d197167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d195452 q = 1) (hb : d196213 q = 1) : d197215 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d195452, d196213, d197215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46796 q ha hb
    | true =>
      simp only [d195452, d196213, d197215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46801 q ha hb
  have h7 (q : Pattern) (ha : d1 q = 1) (hb : d120143 q = 1) : d120143 q = 1 := by
    exact hb
  have h8 (q : Pattern) (ha : d195454 q = 1) (hb : d196215 q = 1) : d197217 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d195454, d196215, d197217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46802 q ha hb
    | true =>
      simp only [d195454, d196215, d197217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d195455 q = 1) (hb : d196216 q = 1) : d197218 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d195455, d196216, d197218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d195455, d196216, d197218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d195456 q = 1) (hb : d196217 q = 1) : d197219 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d195456, d196217, d197219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d195456, d196217, d197219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d195457 q = 1) (hb : d196218 q = 1) : d197220 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d195457, d196218, d197220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d195457, d196218, d197220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d195461 q = 1) (hb : d196222 q = 1) : d197224 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d195461, d196222, d197224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195461, d196222, d197224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46803 q ha hb
  have h13 (q : Pattern) (ha : d1 q = 1) (hb : d120335 q = 1) : d120335 q = 1 := by
    exact hb
  have h14 (q : Pattern) (ha : d195462 q = 1) (hb : d196223 q = 1) : d197225 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d195462, d196223, d197225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d195462, d196223, d197225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d195463 q = 1) (hb : d196224 q = 1) : d197226 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d195463, d196224, d197226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d195463, d196224, d197226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d195464 q = 1) (hb : d196225 q = 1) : d197227 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d195464, d196225, d197227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d195464, d196225, d197227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h17 (q : Pattern) (ha : d195465 q = 1) (hb : d196226 q = 1) : d197228 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d195465, d196226, d197228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d195465, d196226, d197228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d195489 q = 1) (hb : d196252 q = 1) : d197253 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d195489, d196252, d197253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195489, d196252, d197253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46811 q ha hb
  have h19 (q : Pattern) (ha : d1 q = 1) (hb : d120379 q = 1) : d120379 q = 1 := by
    exact hb
  have h20 (q : Pattern) (ha : d195490 q = 1) (hb : d196253 q = 1) : d197254 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d195490, d196253, d197254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d195490, d196253, d197254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d195491 q = 1) (hb : d196254 q = 1) : d197255 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d195491, d196254, d197255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d195491, d196254, d197255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d195492 q = 1) (hb : d196255 q = 1) : d197256 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d195492, d196255, d197256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d195492, d196255, d197256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d195493 q = 1) (hb : d196256 q = 1) : d197257 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d195493, d196256, d197257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d195493, d196256, d197257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d195494 q = 1) (hb : d196257 q = 1) : d197258 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d195494, d196257, d197258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d195494, d196257, d197258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  exact h24 p ha hb
theorem andIntro46813 (p : Pattern) (ha : d195500 p = 1) (hb : d196263 p = 1) : d197264 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d195495 q = 1) (hb : d196258 q = 1) : d197259 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d195495, d196258, d197259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195495, d196258, d197259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46812 q ha hb
  have h2 (q : Pattern) (ha : d195496 q = 1) (hb : d196259 q = 1) : d197260 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d195496, d196259, d197260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195496, d196259, d197260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d195497 q = 1) (hb : d196260 q = 1) : d197261 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d195497, d196260, d197261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195497, d196260, d197261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d195498 q = 1) (hb : d196261 q = 1) : d197262 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d195498, d196261, d197262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195498, d196261, d197262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d195499 q = 1) (hb : d196262 q = 1) : d197263 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d195499, d196262, d197263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195499, d196262, d197263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d195500 q = 1) (hb : d196263 q = 1) : d197264 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d195500, d196263, d197264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195500, d196263, d197264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro46814 (p : Pattern) (ha : d52432 p = 1) (hb : d196265 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52432 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d21189 q = 1) (hb : d52118 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21189, d52118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46791 q ha hb
    | true =>
      simp only [d21189, d52118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21190 q = 1) (hb : d52119 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21190, d52119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21190, d52119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d21191 q = 1) (hb : d52120 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d21191, d52120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d21191, d52120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21192 q = 1) (hb : d52121 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d21192, d52121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21192, d52121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d751 q = 1) (hb : d52428 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d751, d52428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100 q ha hb
    | true =>
      simp only [d751, d52428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d752 q = 1) (hb : d52429 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d752, d52429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d752, d52429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d753 q = 1) (hb : d52430 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d753, d52430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d753, d52430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d754 q = 1) (hb : d52431 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d754, d52431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d754, d52431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d21418 q = 1) (hb : d52432 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d21418, d52432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21418, d52432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d52432 q = 1) (hb : d196265 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d196265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d196265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro46815 (p : Pattern) (ha : d96600 p = 1) (hb : d196271 p = 1) : d197267 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96534 q = 1) (hb : d196266 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d96534, d196266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46814 q ha hb
    | true =>
      simp only [d96534, d196266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35504 q ha hb
  have h2 (q : Pattern) (ha : d96535 q = 1) (hb : d196267 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d96535, d196267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96535, d196267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d96536 q = 1) (hb : d196268 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d96536, d196268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96536, d196268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d96536 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d96536 q = 1) (hb : d196269 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d196269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d196269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d1 q = 1) (hb : d120400 q = 1) : d120400 q = 1 := by
    exact hb
  have h7 (q : Pattern) (ha : d96599 q = 1) (hb : d196270 q = 1) : d197266 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d96599, d196270, d197266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d96599, d196270, d197266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d96600 q = 1) (hb : d196271 q = 1) : d197267 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d96600, d196271, d197267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d96600, d196271, d197267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro46816 (p : Pattern) (ha : d195505 p = 1) (hb : d196277 p = 1) : d197273 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96601 q = 1) (hb : d196272 q = 1) : d197268 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d96601, d196272, d197268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46815 q ha hb
    | true =>
      simp only [d96601, d196272, d197268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d96602 q = 1) (hb : d196273 q = 1) : d197269 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d96602, d196273, d197269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96602, d196273, d197269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1 q = 1) (hb : d120408 q = 1) : d120408 q = 1 := by
    exact hb
  have h4 (q : Pattern) (ha : d195502 q = 1) (hb : d196274 q = 1) : d197270 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d195502, d196274, d197270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d195502, d196274, d197270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d195503 q = 1) (hb : d196275 q = 1) : d197271 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d195503, d196275, d197271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d195503, d196275, d197271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d195504 q = 1) (hb : d196276 q = 1) : d197272 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d195504, d196276, d197272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d195504, d196276, d197272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d195505 q = 1) (hb : d196277 q = 1) : d197273 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d195505, d196277, d197273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195505, d196277, d197273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro46817 (p : Pattern) (ha : d195511 p = 1) (hb : d196283 p = 1) : d197279 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d120416 q = 1) : d120416 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d195506 q = 1) (hb : d196278 q = 1) : d197274 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195506, d196278, d197274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46816 q ha hb
    | true =>
      simp only [d195506, d196278, d197274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d195507 q = 1) (hb : d196279 q = 1) : d197275 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d195507, d196279, d197275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195507, d196279, d197275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d195508 q = 1) (hb : d196280 q = 1) : d197276 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d195508, d196280, d197276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d195508, d196280, d197276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d195509 q = 1) (hb : d196281 q = 1) : d197277 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d195509, d196281, d197277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195509, d196281, d197277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d195510 q = 1) (hb : d196282 q = 1) : d197278 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d195510, d196282, d197278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195510, d196282, d197278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d195511 q = 1) (hb : d196283 q = 1) : d197279 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d195511, d196283, d197279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195511, d196283, d197279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro46818 (p : Pattern) (ha : d195514 p = 1) (hb : d196286 p = 1) : d197282 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96601 q = 1) (hb : d196272 q = 1) : d197268 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d96601, d196272, d197268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46815 q ha hb
    | true =>
      simp only [d96601, d196272, d197268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d96602 q = 1) (hb : d196273 q = 1) : d197269 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d96602, d196273, d197269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96602, d196273, d197269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1 q = 1) (hb : d120408 q = 1) : d120408 q = 1 := by
    exact hb
  have h4 (q : Pattern) (ha : d195502 q = 1) (hb : d196274 q = 1) : d197270 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d195502, d196274, d197270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d195502, d196274, d197270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d195503 q = 1) (hb : d196275 q = 1) : d197271 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d195503, d196275, d197271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d195503, d196275, d197271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d195504 q = 1) (hb : d196276 q = 1) : d197272 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d195504, d196276, d197272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d195504, d196276, d197272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d195514 q = 1) (hb : d196286 q = 1) : d197282 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d195514, d196286, d197282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d195514, d196286, d197282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro46819 (p : Pattern) (ha : d195520 p = 1) (hb : d196292 p = 1) : d197288 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d120416 q = 1) : d120416 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d195506 q = 1) (hb : d196278 q = 1) : d197274 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195506, d196278, d197274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46816 q ha hb
    | true =>
      simp only [d195506, d196278, d197274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d195507 q = 1) (hb : d196279 q = 1) : d197275 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d195507, d196279, d197275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195507, d196279, d197275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d195508 q = 1) (hb : d196280 q = 1) : d197276 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d195508, d196280, d197276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d195508, d196280, d197276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d195509 q = 1) (hb : d196281 q = 1) : d197277 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d195509, d196281, d197277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195509, d196281, d197277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d195510 q = 1) (hb : d196282 q = 1) : d197278 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d195510, d196282, d197278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195510, d196282, d197278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1 q = 1) (hb : d120426 q = 1) : d120426 q = 1 := by
    exact hb
  have h8 (q : Pattern) (ha : d195515 q = 1) (hb : d196287 q = 1) : d197283 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195515, d196287, d197283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46818 q ha hb
    | true =>
      simp only [d195515, d196287, d197283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d195516 q = 1) (hb : d196288 q = 1) : d197284 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d195516, d196288, d197284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195516, d196288, d197284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d195517 q = 1) (hb : d196289 q = 1) : d197285 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d195517, d196289, d197285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d195517, d196289, d197285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d195518 q = 1) (hb : d196290 q = 1) : d197286 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d195518, d196290, d197286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195518, d196290, d197286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d195519 q = 1) (hb : d196291 q = 1) : d197287 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d195519, d196291, d197287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195519, d196291, d197287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d195520 q = 1) (hb : d196292 q = 1) : d197288 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d195520, d196292, d197288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d195520, d196292, d197288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro46820 (p : Pattern) (ha : d195505 p = 1) (hb : d196326 p = 1) : d197313 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96601 q = 1) (hb : d196272 q = 1) : d197268 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d96601, d196272, d197268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46815 q ha hb
    | true =>
      simp only [d96601, d196272, d197268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d96602 q = 1) (hb : d196273 q = 1) : d197269 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d96602, d196273, d197269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96602, d196273, d197269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d195502 q = 1) (hb : d196323 q = 1) : d197310 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d195502, d196323, d197310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d195502, d196323, d197310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d195503 q = 1) (hb : d196324 q = 1) : d197311 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d195503, d196324, d197311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d195503, d196324, d197311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d195504 q = 1) (hb : d196325 q = 1) : d197312 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d195504, d196325, d197312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d195504, d196325, d197312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d195505 q = 1) (hb : d196326 q = 1) : d197313 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d195505, d196326, d197313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195505, d196326, d197313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro46821 (p : Pattern) (ha : d195525 p = 1) (hb : d196297 p = 1) : d197293 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96601 q = 1) (hb : d196272 q = 1) : d197268 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d96601, d196272, d197268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46815 q ha hb
    | true =>
      simp only [d96601, d196272, d197268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d96602 q = 1) (hb : d196273 q = 1) : d197269 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d96602, d196273, d197269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96602, d196273, d197269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1 q = 1) (hb : d120408 q = 1) : d120408 q = 1 := by
    exact hb
  have h4 (q : Pattern) (ha : d195502 q = 1) (hb : d196274 q = 1) : d197270 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d195502, d196274, d197270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d195502, d196274, d197270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d195503 q = 1) (hb : d196275 q = 1) : d197271 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d195503, d196275, d197271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d195503, d196275, d197271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d195524 q = 1) (hb : d196296 q = 1) : d197292 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d195524, d196296, d197292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195524, d196296, d197292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d195525 q = 1) (hb : d196297 q = 1) : d197293 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d195525, d196297, d197293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195525, d196297, d197293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro46822 (p : Pattern) (ha : d195532 p = 1) (hb : d196304 p = 1) : d197300 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96601 q = 1) (hb : d196272 q = 1) : d197268 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d96601, d196272, d197268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46815 q ha hb
    | true =>
      simp only [d96601, d196272, d197268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d96602 q = 1) (hb : d196273 q = 1) : d197269 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d96602, d196273, d197269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96602, d196273, d197269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1 q = 1) (hb : d120408 q = 1) : d120408 q = 1 := by
    exact hb
  have h4 (q : Pattern) (ha : d195502 q = 1) (hb : d196274 q = 1) : d197270 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d195502, d196274, d197270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d195502, d196274, d197270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d195530 q = 1) (hb : d196302 q = 1) : d197298 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d195530, d196302, d197298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195530, d196302, d197298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d195531 q = 1) (hb : d196303 q = 1) : d197299 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d195531, d196303, d197299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d195531, d196303, d197299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d195532 q = 1) (hb : d196304 q = 1) : d197300 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d195532, d196304, d197300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195532, d196304, d197300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro46823 (p : Pattern) (ha : d21487 p = 1) (hb : d52289 p = 1) : d0 p = 1 := by
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
  have h3 (q : Pattern) (ha : d9581 q = 1) (hb : d52112 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d9581, d52112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35525 q ha hb
    | true =>
      simp only [d9581, d52112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d9582 q = 1) (hb : d52113 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d9582, d52113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9582, d52113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d9593 q = 1) (hb : d52280 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d9593, d52280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9593, d52280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d52286 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d9594 q = 1) (hb : d52287 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d9594, d52287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9594, d52287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d9595 q = 1) (hb : d52288 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d9595, d52288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d9595, d52288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d52116 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d21487 q = 1) (hb : d52289 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d21487, d52289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d21487, d52289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro46824 (p : Pattern) (ha : d52294 p = 1) (hb : d196308 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52294 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d21488 q = 1) (hb : d52290 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21488, d52290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46823 q ha hb
    | true =>
      simp only [d21488, d52290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21489 q = 1) (hb : d52291 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21489, d52291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21489, d52291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d21490 q = 1) (hb : d52292 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d21490, d52292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d21490, d52292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21491 q = 1) (hb : d52293 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d21491, d52293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21491, d52293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d21189 q = 1) (hb : d52118 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21189, d52118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46791 q ha hb
    | true =>
      simp only [d21189, d52118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d21190 q = 1) (hb : d52119 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21190, d52119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21190, d52119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d21191 q = 1) (hb : d52120 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d21191, d52120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d21191, d52120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d21192 q = 1) (hb : d52121 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d21192, d52121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d21192, d52121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d21492 q = 1) (hb : d52294 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d21492, d52294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21492, d52294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d52294 q = 1) (hb : d196308 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d196308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d196308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro46825 (p : Pattern) (ha : d113136 p = 1) (hb : d196265 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d113136 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d21189 q = 1) (hb : d101083 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21189, d101083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46115 q ha hb
    | true =>
      simp only [d21189, d101083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21190 q = 1) (hb : d101085 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21190, d101085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21190, d101085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d21191 q = 1) (hb : d113134 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d21191, d113134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d21191, d113134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21192 q = 1) (hb : d113135 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d21192, d113135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21192, d113135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d751 q = 1) (hb : d52428 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d751, d52428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100 q ha hb
    | true =>
      simp only [d751, d52428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d752 q = 1) (hb : d52429 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d752, d52429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d752, d52429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d753 q = 1) (hb : d52430 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d753, d52430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d753, d52430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d754 q = 1) (hb : d52431 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d754, d52431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d754, d52431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d21418 q = 1) (hb : d113136 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d21418, d113136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21418, d113136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d113136 q = 1) (hb : d196265 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d196265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d196265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro46826 (p : Pattern) (ha : d195540 p = 1) (hb : d196314 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d195536 q = 1) (hb : d196309 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d195536, d196309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46824 q ha hb
    | true =>
      simp only [d195536, d196309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46825 q ha hb
  have h2 (q : Pattern) (ha : d195537 q = 1) (hb : d196310 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d195537, d196310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195537, d196310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d195538 q = 1) (hb : d196311 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d195538, d196311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195538, d196311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d195538 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d195538 q = 1) (hb : d196312 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d196312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d196312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d96534 q = 1) (hb : d196266 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d96534, d196266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46814 q ha hb
    | true =>
      simp only [d96534, d196266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35504 q ha hb
  have h7 (q : Pattern) (ha : d96535 q = 1) (hb : d196267 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d96535, d196267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96535, d196267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d96536 q = 1) (hb : d196268 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d96536, d196268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96536, d196268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d96536 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d96536 q = 1) (hb : d196269 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d196269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d196269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d195539 q = 1) (hb : d196313 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d195539, d196313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d195539, d196313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d195540 q = 1) (hb : d196314 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d195540, d196314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d195540, d196314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h12 p ha hb
theorem andIntro46827 (p : Pattern) (ha : d195546 p = 1) (hb : d196320 p = 1) : d197307 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d195541 q = 1) (hb : d196315 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d195541, d196315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46826 q ha hb
    | true =>
      simp only [d195541, d196315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d195542 q = 1) (hb : d196316 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d195542, d196316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195542, d196316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d96601 q = 1) (hb : d196272 q = 1) : d197268 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d96601, d196272, d197268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46815 q ha hb
    | true =>
      simp only [d96601, d196272, d197268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d96602 q = 1) (hb : d196273 q = 1) : d197269 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d96602, d196273, d197269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96602, d196273, d197269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d195543 q = 1) (hb : d196317 q = 1) : d197304 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d195543, d196317, d197304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d195543, d196317, d197304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d195544 q = 1) (hb : d196318 q = 1) : d197305 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d195544, d196318, d197305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d195544, d196318, d197305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d195545 q = 1) (hb : d196319 q = 1) : d197306 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d195545, d196319, d197306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d195545, d196319, d197306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d195546 q = 1) (hb : d196320 q = 1) : d197307 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d195546, d196320, d197307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195546, d196320, d197307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro46828 (p : Pattern) (ha : d195553 p = 1) (hb : d196332 p = 1) : d197319 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d120439 q = 1) : d120439 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d195526 q = 1) (hb : d196298 q = 1) : d197294 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195526, d196298, d197294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46821 q ha hb
    | true =>
      simp only [d195526, d196298, d197294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d195527 q = 1) (hb : d196299 q = 1) : d197295 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d195527, d196299, d197295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195527, d196299, d197295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d195528 q = 1) (hb : d196300 q = 1) : d197296 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d195528, d196300, d197296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d195528, d196300, d197296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d195529 q = 1) (hb : d196301 q = 1) : d197297 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d195529, d196301, d197297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195529, d196301, d197297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1 q = 1) (hb : d120449 q = 1) : d120449 q = 1 := by
    exact hb
  have h7 (q : Pattern) (ha : d195533 q = 1) (hb : d196305 q = 1) : d197301 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195533, d196305, d197301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46822 q ha hb
    | true =>
      simp only [d195533, d196305, d197301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d195534 q = 1) (hb : d196306 q = 1) : d197302 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d195534, d196306, d197302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195534, d196306, d197302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d195535 q = 1) (hb : d196307 q = 1) : d197303 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d195535, d196307, d197303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d195535, d196307, d197303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d195547 q = 1) (hb : d196321 q = 1) : d197308 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195547, d196321, d197308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46827 q ha hb
    | true =>
      simp only [d195547, d196321, d197308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46816 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d195506 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d195548 q = 1) (hb : d196322 q = 1) : d197309 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d195548, d196322, d197309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d195548, d196322, d197309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d195506 q = 1) (hb : d196327 q = 1) : d197314 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195506, d196327, d197314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46820 q ha hb
    | true =>
      simp only [d195506, d196327, d197314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d195549 q = 1) (hb : d196328 q = 1) : d197315 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d195549, d196328, d197315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d195549, d196328, d197315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d195550 q = 1) (hb : d196329 q = 1) : d197316 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d195550, d196329, d197316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d195550, d196329, d197316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d195551 q = 1) (hb : d196330 q = 1) : d197317 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d195551, d196330, d197317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d195551, d196330, d197317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d195552 q = 1) (hb : d196331 q = 1) : d197318 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d195552, d196331, d197318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d195552, d196331, d197318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d195553 q = 1) (hb : d196332 q = 1) : d197319 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d195553, d196332, d197319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195553, d196332, d197319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro46829 (p : Pattern) (ha : d195514 p = 1) (hb : d196345 p = 1) : d197332 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96601 q = 1) (hb : d196272 q = 1) : d197268 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d96601, d196272, d197268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46815 q ha hb
    | true =>
      simp only [d96601, d196272, d197268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d96602 q = 1) (hb : d196273 q = 1) : d197269 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d96602, d196273, d197269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96602, d196273, d197269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d195502 q = 1) (hb : d196323 q = 1) : d197310 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d195502, d196323, d197310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d195502, d196323, d197310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d195503 q = 1) (hb : d196324 q = 1) : d197311 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d195503, d196324, d197311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d195503, d196324, d197311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d195504 q = 1) (hb : d196325 q = 1) : d197312 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d195504, d196325, d197312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d195504, d196325, d197312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d195514 q = 1) (hb : d196345 q = 1) : d197332 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d195514, d196345, d197332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d195514, d196345, d197332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro46830 (p : Pattern) (ha : d195554 p = 1) (hb : d196333 p = 1) : d197320 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96601 q = 1) (hb : d196272 q = 1) : d197268 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d96601, d196272, d197268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46815 q ha hb
    | true =>
      simp only [d96601, d196272, d197268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d96602 q = 1) (hb : d196273 q = 1) : d197269 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d96602, d196273, d197269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96602, d196273, d197269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1 q = 1) (hb : d120408 q = 1) : d120408 q = 1 := by
    exact hb
  have h4 (q : Pattern) (ha : d195502 q = 1) (hb : d196274 q = 1) : d197270 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d195502, d196274, d197270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d195502, d196274, d197270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d195503 q = 1) (hb : d196275 q = 1) : d197271 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d195503, d196275, d197271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d195503, d196275, d197271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d195524 q = 1) (hb : d196296 q = 1) : d197292 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d195524, d196296, d197292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195524, d196296, d197292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d195554 q = 1) (hb : d196333 q = 1) : d197320 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d195554, d196333, d197320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d195554, d196333, d197320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro46831 (p : Pattern) (ha : d195559 p = 1) (hb : d196338 p = 1) : d197325 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96601 q = 1) (hb : d196272 q = 1) : d197268 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d96601, d196272, d197268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46815 q ha hb
    | true =>
      simp only [d96601, d196272, d197268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d96602 q = 1) (hb : d196273 q = 1) : d197269 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d96602, d196273, d197269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96602, d196273, d197269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1 q = 1) (hb : d120408 q = 1) : d120408 q = 1 := by
    exact hb
  have h4 (q : Pattern) (ha : d195502 q = 1) (hb : d196274 q = 1) : d197270 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d195502, d196274, d197270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d195502, d196274, d197270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d195530 q = 1) (hb : d196302 q = 1) : d197298 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d195530, d196302, d197298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195530, d196302, d197298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d195531 q = 1) (hb : d196303 q = 1) : d197299 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d195531, d196303, d197299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d195531, d196303, d197299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d195559 q = 1) (hb : d196338 q = 1) : d197325 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d195559, d196338, d197325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d195559, d196338, d197325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro46832 (p : Pattern) (ha : d195563 p = 1) (hb : d196342 p = 1) : d197329 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d195541 q = 1) (hb : d196315 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d195541, d196315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46826 q ha hb
    | true =>
      simp only [d195541, d196315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d195542 q = 1) (hb : d196316 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d195542, d196316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195542, d196316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d96601 q = 1) (hb : d196272 q = 1) : d197268 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d96601, d196272, d197268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46815 q ha hb
    | true =>
      simp only [d96601, d196272, d197268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d96602 q = 1) (hb : d196273 q = 1) : d197269 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d96602, d196273, d197269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96602, d196273, d197269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d195543 q = 1) (hb : d196317 q = 1) : d197304 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d195543, d196317, d197304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d195543, d196317, d197304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d195544 q = 1) (hb : d196318 q = 1) : d197305 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d195544, d196318, d197305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d195544, d196318, d197305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d195545 q = 1) (hb : d196319 q = 1) : d197306 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d195545, d196319, d197306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d195545, d196319, d197306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d195563 q = 1) (hb : d196342 q = 1) : d197329 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d195563, d196342, d197329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d195563, d196342, d197329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro46833 (p : Pattern) (ha : d195570 p = 1) (hb : d196351 p = 1) : d197338 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d120439 q = 1) : d120439 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d195526 q = 1) (hb : d196298 q = 1) : d197294 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195526, d196298, d197294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46821 q ha hb
    | true =>
      simp only [d195526, d196298, d197294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d195527 q = 1) (hb : d196299 q = 1) : d197295 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d195527, d196299, d197295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195527, d196299, d197295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d195528 q = 1) (hb : d196300 q = 1) : d197296 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d195528, d196300, d197296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d195528, d196300, d197296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d195529 q = 1) (hb : d196301 q = 1) : d197297 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d195529, d196301, d197297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195529, d196301, d197297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1 q = 1) (hb : d120449 q = 1) : d120449 q = 1 := by
    exact hb
  have h7 (q : Pattern) (ha : d195533 q = 1) (hb : d196305 q = 1) : d197301 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195533, d196305, d197301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46822 q ha hb
    | true =>
      simp only [d195533, d196305, d197301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d195534 q = 1) (hb : d196306 q = 1) : d197302 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d195534, d196306, d197302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195534, d196306, d197302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d195535 q = 1) (hb : d196307 q = 1) : d197303 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d195535, d196307, d197303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d195535, d196307, d197303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d195547 q = 1) (hb : d196321 q = 1) : d197308 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195547, d196321, d197308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46827 q ha hb
    | true =>
      simp only [d195547, d196321, d197308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46816 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d195506 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d195548 q = 1) (hb : d196322 q = 1) : d197309 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d195548, d196322, d197309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d195548, d196322, d197309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d195506 q = 1) (hb : d196327 q = 1) : d197314 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195506, d196327, d197314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46820 q ha hb
    | true =>
      simp only [d195506, d196327, d197314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d195549 q = 1) (hb : d196328 q = 1) : d197315 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d195549, d196328, d197315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d195549, d196328, d197315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d195550 q = 1) (hb : d196329 q = 1) : d197316 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d195550, d196329, d197316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d195550, d196329, d197316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d195551 q = 1) (hb : d196330 q = 1) : d197317 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d195551, d196330, d197317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d195551, d196330, d197317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d195552 q = 1) (hb : d196331 q = 1) : d197318 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d195552, d196331, d197318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d195552, d196331, d197318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d1 q = 1) (hb : d120487 q = 1) : d120487 q = 1 := by
    exact hb
  have h19 (q : Pattern) (ha : d195555 q = 1) (hb : d196334 q = 1) : d197321 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195555, d196334, d197321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46830 q ha hb
    | true =>
      simp only [d195555, d196334, d197321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d195556 q = 1) (hb : d196335 q = 1) : d197322 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d195556, d196335, d197322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195556, d196335, d197322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d195557 q = 1) (hb : d196336 q = 1) : d197323 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d195557, d196336, d197323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d195557, d196336, d197323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d195558 q = 1) (hb : d196337 q = 1) : d197324 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d195558, d196337, d197324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195558, d196337, d197324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d1 q = 1) (hb : d120493 q = 1) : d120493 q = 1 := by
    exact hb
  have h24 (q : Pattern) (ha : d195560 q = 1) (hb : d196339 q = 1) : d197326 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195560, d196339, d197326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46831 q ha hb
    | true =>
      simp only [d195560, d196339, d197326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d195561 q = 1) (hb : d196340 q = 1) : d197327 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d195561, d196340, d197327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195561, d196340, d197327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
  have h26 (q : Pattern) (ha : d195562 q = 1) (hb : d196341 q = 1) : d197328 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d195562, d196341, d197328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d195562, d196341, d197328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d195564 q = 1) (hb : d196343 q = 1) : d197330 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195564, d196343, d197330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46832 q ha hb
    | true =>
      simp only [d195564, d196343, d197330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46818 q ha hb
  have h28 (q : Pattern) (ha : d0 q = 1) (hb : d195515 q = 1) : d0 q = 1 := by
    exact ha
  have h29 (q : Pattern) (ha : d195565 q = 1) (hb : d196344 q = 1) : d197331 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d195565, d196344, d197331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
    | true =>
      simp only [d195565, d196344, d197331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q hb ha
  have h30 (q : Pattern) (ha : d195515 q = 1) (hb : d196346 q = 1) : d197333 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195515, d196346, d197333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46829 q ha hb
    | true =>
      simp only [d195515, d196346, d197333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h31 (q : Pattern) (ha : d195566 q = 1) (hb : d196347 q = 1) : d197334 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d195566, d196347, d197334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
    | true =>
      simp only [d195566, d196347, d197334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h32 (q : Pattern) (ha : d195567 q = 1) (hb : d196348 q = 1) : d197335 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d195567, d196348, d197335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
    | true =>
      simp only [d195567, d196348, d197335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
  have h33 (q : Pattern) (ha : d195568 q = 1) (hb : d196349 q = 1) : d197336 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d195568, d196349, d197336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d195568, d196349, d197336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h32 q ha hb
  have h34 (q : Pattern) (ha : d195569 q = 1) (hb : d196350 q = 1) : d197337 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d195569, d196350, d197337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d195569, d196350, d197337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h33 q ha hb
  have h35 (q : Pattern) (ha : d195570 q = 1) (hb : d196351 q = 1) : d197338 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d195570, d196351, d197338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d195570, d196351, d197338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h34 q ha hb
  exact h35 p ha hb
theorem andIntro46834 (p : Pattern) (ha : d195572 p = 1) (hb : d196353 p = 1) : d197340 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d120416 q = 1) : d120416 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d195506 q = 1) (hb : d196278 q = 1) : d197274 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195506, d196278, d197274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46816 q ha hb
    | true =>
      simp only [d195506, d196278, d197274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d195507 q = 1) (hb : d196279 q = 1) : d197275 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d195507, d196279, d197275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195507, d196279, d197275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d195508 q = 1) (hb : d196280 q = 1) : d197276 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d195508, d196280, d197276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d195508, d196280, d197276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d195509 q = 1) (hb : d196281 q = 1) : d197277 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d195509, d196281, d197277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195509, d196281, d197277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d195510 q = 1) (hb : d196282 q = 1) : d197278 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d195510, d196282, d197278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195510, d196282, d197278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1 q = 1) (hb : d120518 q = 1) : d120518 q = 1 := by
    exact hb
  have h8 (q : Pattern) (ha : d195572 q = 1) (hb : d196353 q = 1) : d197340 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d195572, d196353, d197340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d195572, d196353, d197340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro46835 (p : Pattern) (ha : d195579 p = 1) (hb : d196360 p = 1) : d197347 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d195564 q = 1) (hb : d196343 q = 1) : d197330 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195564, d196343, d197330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46832 q ha hb
    | true =>
      simp only [d195564, d196343, d197330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46818 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d195515 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d195565 q = 1) (hb : d196344 q = 1) : d197331 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d195565, d196344, d197331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d195565, d196344, d197331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d195515 q = 1) (hb : d196346 q = 1) : d197333 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195515, d196346, d197333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46829 q ha hb
    | true =>
      simp only [d195515, d196346, d197333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d195566 q = 1) (hb : d196347 q = 1) : d197334 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d195566, d196347, d197334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d195566, d196347, d197334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d195567 q = 1) (hb : d196348 q = 1) : d197335 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d195567, d196348, d197335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d195567, d196348, d197335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d195577 q = 1) (hb : d196358 q = 1) : d197345 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d195577, d196358, d197345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195577, d196358, d197345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d195578 q = 1) (hb : d196359 q = 1) : d197346 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d195578, d196359, d197346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195578, d196359, d197346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d195579 q = 1) (hb : d196360 q = 1) : d197347 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d195579, d196360, d197347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195579, d196360, d197347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro46836 (p : Pattern) (ha : d52594 p = 1) (hb : d196367 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52594 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d21314 q = 1) (hb : d52178 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21314, d52178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d21314, d52178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46791 q ha hb
  have h3 (q : Pattern) (ha : d21189 q = 1) (hb : d52118 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21189, d52118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46791 q ha hb
    | true =>
      simp only [d21189, d52118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d21315 q = 1) (hb : d52179 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21315, d52179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21315, d52179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21190 q = 1) (hb : d52119 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21190, d52119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21190, d52119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d21316 q = 1) (hb : d52180 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d21316, d52180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21316, d52180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d21317 q = 1) (hb : d52181 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d21317, d52181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21317, d52181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d971 q = 1) (hb : d52590 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d971, d52590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d971, d52590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100 q ha hb
  have h9 (q : Pattern) (ha : d751 q = 1) (hb : d52428 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d751, d52428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100 q ha hb
    | true =>
      simp only [d751, d52428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d972 q = 1) (hb : d52591 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d972, d52591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d972, d52591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d752 q = 1) (hb : d52429 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d752, d52429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d752, d52429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h12 (q : Pattern) (ha : d973 q = 1) (hb : d52592 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d973, d52592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d973, d52592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d974 q = 1) (hb : d52593 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d974, d52593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d974, d52593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h14 (q : Pattern) (ha : d21623 q = 1) (hb : d52594 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d21623, d52594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21623, d52594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d52594 q = 1) (hb : d196367 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d196367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d196367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  exact h15 p ha hb
theorem andIntro46837 (p : Pattern) (ha : d96688 p = 1) (hb : d196381 p = 1) : d197354 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96680 q = 1) (hb : d196372 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d96680, d196372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46836 q ha hb
    | true =>
      simp only [d96680, d196372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35510 q ha hb
  have h2 (q : Pattern) (ha : d96681 q = 1) (hb : d196373 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d96681, d196373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96681, d196373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d96682 q = 1) (hb : d196374 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d96682, d196374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96682, d196374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d96682 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d96682 q = 1) (hb : d196375 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d196375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d196375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d1 q = 1) (hb : d120565 q = 1) : d120565 q = 1 := by
    exact hb
  have h7 (q : Pattern) (ha : d96687 q = 1) (hb : d196380 q = 1) : d197353 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d96687, d196380, d197353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d96687, d196380, d197353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d96688 q = 1) (hb : d196381 q = 1) : d197354 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d96688, d196381, d197354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d96688, d196381, d197354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro46838 (p : Pattern) (ha : d52367 p = 1) (hb : d196366 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52367 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d21617 q = 1) (hb : d52363 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21617, d52363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d21617, d52363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46823 q ha hb
  have h3 (q : Pattern) (ha : d21488 q = 1) (hb : d52290 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21488, d52290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46823 q ha hb
    | true =>
      simp only [d21488, d52290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d21618 q = 1) (hb : d52364 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21618, d52364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21618, d52364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21489 q = 1) (hb : d52291 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21489, d52291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21489, d52291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d21619 q = 1) (hb : d52365 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d21619, d52365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21619, d52365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d21620 q = 1) (hb : d52366 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d21620, d52366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21620, d52366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d21314 q = 1) (hb : d52178 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21314, d52178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d21314, d52178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46791 q ha hb
  have h9 (q : Pattern) (ha : d21189 q = 1) (hb : d52118 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21189, d52118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46791 q ha hb
    | true =>
      simp only [d21189, d52118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d21315 q = 1) (hb : d52179 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21315, d52179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d21315, d52179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d21190 q = 1) (hb : d52119 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21190, d52119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d21190, d52119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h12 (q : Pattern) (ha : d21316 q = 1) (hb : d52180 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d21316, d52180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d21316, d52180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d21317 q = 1) (hb : d52181 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d21317, d52181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d21317, d52181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h14 (q : Pattern) (ha : d21621 q = 1) (hb : d52367 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d21621, d52367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21621, d52367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d52367 q = 1) (hb : d196366 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d196366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d196366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  exact h15 p ha hb
theorem andIntro46839 (p : Pattern) (ha : d113218 p = 1) (hb : d196367 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d113218 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d21314 q = 1) (hb : d113214 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21314, d113214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d21314, d113214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46115 q ha hb
  have h3 (q : Pattern) (ha : d21189 q = 1) (hb : d101083 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21189, d101083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46115 q ha hb
    | true =>
      simp only [d21189, d101083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d21315 q = 1) (hb : d113215 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21315, d113215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21315, d113215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21190 q = 1) (hb : d101085 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21190, d101085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21190, d101085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d21316 q = 1) (hb : d113216 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d21316, d113216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21316, d113216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d21317 q = 1) (hb : d113217 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d21317, d113217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21317, d113217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d971 q = 1) (hb : d52590 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d971, d52590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d971, d52590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100 q ha hb
  have h9 (q : Pattern) (ha : d751 q = 1) (hb : d52428 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d751, d52428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100 q ha hb
    | true =>
      simp only [d751, d52428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d972 q = 1) (hb : d52591 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d972, d52591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d972, d52591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d752 q = 1) (hb : d52429 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d752, d52429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d752, d52429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h12 (q : Pattern) (ha : d973 q = 1) (hb : d52592 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d973, d52592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d973, d52592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d974 q = 1) (hb : d52593 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d974, d52593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d974, d52593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h14 (q : Pattern) (ha : d21623 q = 1) (hb : d113218 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d21623, d113218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21623, d113218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d113218 q = 1) (hb : d196367 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d196367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d196367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  exact h15 p ha hb
theorem andIntro46840 (p : Pattern) (ha : d195589 p = 1) (hb : d196377 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d195585 q = 1) (hb : d196368 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d195585, d196368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46838 q ha hb
    | true =>
      simp only [d195585, d196368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46839 q ha hb
  have h2 (q : Pattern) (ha : d195586 q = 1) (hb : d196369 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d195586, d196369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195586, d196369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d195587 q = 1) (hb : d196370 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d195587, d196370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195587, d196370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d195587 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d195587 q = 1) (hb : d196371 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d196371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d196371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d96680 q = 1) (hb : d196372 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d96680, d196372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46836 q ha hb
    | true =>
      simp only [d96680, d196372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35510 q ha hb
  have h7 (q : Pattern) (ha : d96681 q = 1) (hb : d196373 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d96681, d196373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96681, d196373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d96682 q = 1) (hb : d196374 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d96682, d196374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96682, d196374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d96682 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d96682 q = 1) (hb : d196375 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d196375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d196375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d195588 q = 1) (hb : d196376 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d195588, d196376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d195588, d196376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d195589 q = 1) (hb : d196377 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d195589, d196377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d195589, d196377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h12 p ha hb
theorem andIntro46841 (p : Pattern) (ha : d195595 p = 1) (hb : d196387 p = 1) : d197360 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d195590 q = 1) (hb : d196378 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d195590, d196378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46840 q ha hb
    | true =>
      simp only [d195590, d196378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d195591 q = 1) (hb : d196379 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d195591, d196379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195591, d196379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d96689 q = 1) (hb : d196382 q = 1) : d197355 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d96689, d196382, d197355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46837 q ha hb
    | true =>
      simp only [d96689, d196382, d197355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d96690 q = 1) (hb : d196383 q = 1) : d197356 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d96690, d196383, d197356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96690, d196383, d197356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d195592 q = 1) (hb : d196384 q = 1) : d197357 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d195592, d196384, d197357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d195592, d196384, d197357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d195593 q = 1) (hb : d196385 q = 1) : d197358 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d195593, d196385, d197358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d195593, d196385, d197358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d195594 q = 1) (hb : d196386 q = 1) : d197359 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d195594, d196386, d197359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d195594, d196386, d197359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d195595 q = 1) (hb : d196387 q = 1) : d197360 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d195595, d196387, d197360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d195595, d196387, d197360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro46842 (p : Pattern) (ha : d195599 p = 1) (hb : d196391 p = 1) : d197364 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96689 q = 1) (hb : d196382 q = 1) : d197355 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d96689, d196382, d197355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46837 q ha hb
    | true =>
      simp only [d96689, d196382, d197355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d96690 q = 1) (hb : d196383 q = 1) : d197356 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d96690, d196383, d197356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96690, d196383, d197356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1 q = 1) (hb : d120569 q = 1) : d120569 q = 1 := by
    exact hb
  have h4 (q : Pattern) (ha : d195596 q = 1) (hb : d196388 q = 1) : d197361 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d195596, d196388, d197361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d195596, d196388, d197361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d195597 q = 1) (hb : d196389 q = 1) : d197362 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d195597, d196389, d197362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d195597, d196389, d197362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d195598 q = 1) (hb : d196390 q = 1) : d197363 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d195598, d196390, d197363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d195598, d196390, d197363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d195599 q = 1) (hb : d196391 q = 1) : d197364 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d195599, d196391, d197364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d195599, d196391, d197364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro46843 (p : Pattern) (ha : d195599 p = 1) (hb : d196397 p = 1) : d197370 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96689 q = 1) (hb : d196382 q = 1) : d197355 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d96689, d196382, d197355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46837 q ha hb
    | true =>
      simp only [d96689, d196382, d197355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d96690 q = 1) (hb : d196383 q = 1) : d197356 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d96690, d196383, d197356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96690, d196383, d197356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d195596 q = 1) (hb : d196394 q = 1) : d197367 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d195596, d196394, d197367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d195596, d196394, d197367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d195597 q = 1) (hb : d196395 q = 1) : d197368 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d195597, d196395, d197368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d195597, d196395, d197368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d195598 q = 1) (hb : d196396 q = 1) : d197369 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d195598, d196396, d197369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d195598, d196396, d197369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d195599 q = 1) (hb : d196397 q = 1) : d197370 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d195599, d196397, d197370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d195599, d196397, d197370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro46844 (p : Pattern) (ha : d195607 p = 1) (hb : d196403 p = 1) : d197376 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d195600 q = 1) (hb : d196392 q = 1) : d197365 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195600, d196392, d197365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46841 q ha hb
    | true =>
      simp only [d195600, d196392, d197365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46842 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d195601 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d195602 q = 1) (hb : d196393 q = 1) : d197366 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d195602, d196393, d197366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d195602, d196393, d197366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d195601 q = 1) (hb : d196398 q = 1) : d197371 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195601, d196398, d197371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46843 q ha hb
    | true =>
      simp only [d195601, d196398, d197371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d195603 q = 1) (hb : d196399 q = 1) : d197372 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d195603, d196399, d197372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d195603, d196399, d197372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d195604 q = 1) (hb : d196400 q = 1) : d197373 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d195604, d196400, d197373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d195604, d196400, d197373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d195605 q = 1) (hb : d196401 q = 1) : d197374 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d195605, d196401, d197374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195605, d196401, d197374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d195606 q = 1) (hb : d196402 q = 1) : d197375 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d195606, d196402, d197375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195606, d196402, d197375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d195607 q = 1) (hb : d196403 q = 1) : d197376 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d195607, d196403, d197376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195607, d196403, d197376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro46845 (p : Pattern) (ha : d195613 p = 1) (hb : d196409 p = 1) : d197382 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d195512 q = 1) (hb : d196284 q = 1) : d197280 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d195512, d196284, d197280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195512, d196284, d197280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46817 q ha hb
  have h2 (q : Pattern) (ha : d195513 q = 1) (hb : d196285 q = 1) : d197281 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d195513, d196285, d197281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d195513, d196285, d197281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d195521 q = 1) (hb : d196293 q = 1) : d197289 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d195521, d196293, d197289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46817 q ha hb
    | true =>
      simp only [d195521, d196293, d197289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46819 q ha hb
  have h4 (q : Pattern) (ha : d195522 q = 1) (hb : d196294 q = 1) : d197290 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d195522, d196294, d197290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d195522, d196294, d197290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d195523 q = 1) (hb : d196295 q = 1) : d197291 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d195523, d196295, d197291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d195523, d196295, d197291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d195571 q = 1) (hb : d196352 q = 1) : d197339 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d195571, d196352, d197339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46828 q ha hb
    | true =>
      simp only [d195571, d196352, d197339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46833 q ha hb
  have h7 (q : Pattern) (ha : d1 q = 1) (hb : d120525 q = 1) : d120525 q = 1 := by
    exact hb
  have h8 (q : Pattern) (ha : d195573 q = 1) (hb : d196354 q = 1) : d197341 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d195573, d196354, d197341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46834 q ha hb
    | true =>
      simp only [d195573, d196354, d197341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d195574 q = 1) (hb : d196355 q = 1) : d197342 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d195574, d196355, d197342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d195574, d196355, d197342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d195575 q = 1) (hb : d196356 q = 1) : d197343 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d195575, d196356, d197343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d195575, d196356, d197343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d195576 q = 1) (hb : d196357 q = 1) : d197344 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d195576, d196357, d197344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d195576, d196357, d197344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d195580 q = 1) (hb : d196361 q = 1) : d197348 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d195580, d196361, d197348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195580, d196361, d197348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46835 q ha hb
  have h13 (q : Pattern) (ha : d1 q = 1) (hb : d120535 q = 1) : d120535 q = 1 := by
    exact hb
  have h14 (q : Pattern) (ha : d195581 q = 1) (hb : d196362 q = 1) : d197349 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d195581, d196362, d197349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d195581, d196362, d197349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d195582 q = 1) (hb : d196363 q = 1) : d197350 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d195582, d196363, d197350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d195582, d196363, d197350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d195583 q = 1) (hb : d196364 q = 1) : d197351 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d195583, d196364, d197351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d195583, d196364, d197351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h17 (q : Pattern) (ha : d195584 q = 1) (hb : d196365 q = 1) : d197352 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d195584, d196365, d197352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d195584, d196365, d197352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d195608 q = 1) (hb : d196404 q = 1) : d197377 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d195608, d196404, d197377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195608, d196404, d197377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46844 q ha hb
  have h19 (q : Pattern) (ha : d1 q = 1) (hb : d120601 q = 1) : d120601 q = 1 := by
    exact hb
  have h20 (q : Pattern) (ha : d195609 q = 1) (hb : d196405 q = 1) : d197378 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d195609, d196405, d197378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d195609, d196405, d197378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d195610 q = 1) (hb : d196406 q = 1) : d197379 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d195610, d196406, d197379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d195610, d196406, d197379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d195611 q = 1) (hb : d196407 q = 1) : d197380 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d195611, d196407, d197380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d195611, d196407, d197380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d195612 q = 1) (hb : d196408 q = 1) : d197381 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d195612, d196408, d197381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d195612, d196408, d197381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d195613 q = 1) (hb : d196409 q = 1) : d197382 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d195613, d196409, d197382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d195613, d196409, d197382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  exact h24 p ha hb
theorem andIntro46846 (p : Pattern) (ha : d195619 p = 1) (hb : d196415 p = 1) : d197388 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d195614 q = 1) (hb : d196410 q = 1) : d197383 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d195614, d196410, d197383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195614, d196410, d197383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46845 q ha hb
  have h2 (q : Pattern) (ha : d195615 q = 1) (hb : d196411 q = 1) : d197384 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d195615, d196411, d197384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195615, d196411, d197384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d195616 q = 1) (hb : d196412 q = 1) : d197385 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d195616, d196412, d197385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195616, d196412, d197385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d195617 q = 1) (hb : d196413 q = 1) : d197386 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d195617, d196413, d197386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195617, d196413, d197386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d195618 q = 1) (hb : d196414 q = 1) : d197387 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d195618, d196414, d197387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195618, d196414, d197387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d195619 q = 1) (hb : d196415 q = 1) : d197388 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d195619, d196415, d197388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195619, d196415, d197388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro46847 (p : Pattern) (ha : d13024 p = 1) (hb : d52701 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d1094 q = 1) (hb : d52675 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1094, d52675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41 q ha hb
    | true =>
      simp only [d1094, d52675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro148 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1095 q = 1) (hb : d52676 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1095, d52676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1095, d52676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d51870 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d9452 q = 1) (hb : d52685 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d9452, d52685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35483 q ha hb
    | true =>
      simp only [d9452, d52685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9453 q = 1) (hb : d52686 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d9453, d52686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9453, d52686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d9795 q = 1) (hb : d52687 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d9795, d52687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9795, d52687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d133 q = 1) (hb : d51984 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d133, d51984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18 q ha hb
    | true =>
      simp only [d133, d51984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d134 q = 1) (hb : d51985 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d134, d51985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d134, d51985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d51872 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d9796 q = 1) (hb : d51986 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d9796, d51986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d9796, d51986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d9797 q = 1) (hb : d52688 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d9797, d52688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9797, d52688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d9798 q = 1) (hb : d52689 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d9798, d52689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d9798, d52689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d52700 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d13024 q = 1) (hb : d52701 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d13024, d52701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d13024, d52701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h14 p ha hb
theorem andIntro46848 (p : Pattern) (ha : d21747 p = 1) (hb : d52690 p = 1) : d0 p = 1 := by
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
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52674 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d9581 q = 1) (hb : d52675 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d9581, d52675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35525 q ha hb
    | true =>
      simp only [d9581, d52675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9582 q = 1) (hb : d52676 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d9582, d52676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9582, d52676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d9768 q = 1) (hb : d52677 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d9768, d52677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9768, d52677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d52286 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d9769 q = 1) (hb : d52678 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d9769, d52678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9769, d52678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d9770 q = 1) (hb : d52679 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d9770, d52679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d9770, d52679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d52689 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d21747 q = 1) (hb : d52690 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d21747, d52690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d21747, d52690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro46849 (p : Pattern) (ha : d52706 p = 1) (hb : d196418 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52706 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d21748 q = 1) (hb : d52691 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21748, d52691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46848 q ha hb
    | true =>
      simp only [d21748, d52691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21749 q = 1) (hb : d52692 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21749, d52692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21749, d52692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d21750 q = 1) (hb : d52693 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d21750, d52693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d21750, d52693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21751 q = 1) (hb : d52694 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d21751, d52694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21751, d52694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d13025 q = 1) (hb : d52702 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13025, d52702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46847 q ha hb
    | true =>
      simp only [d13025, d52702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d13026 q = 1) (hb : d52703 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13026, d52703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13026, d52703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d13027 q = 1) (hb : d52704 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13027, d52704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d13027, d52704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d13028 q = 1) (hb : d52705 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13028, d52705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d13028, d52705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d21752 q = 1) (hb : d52706 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d21752, d52706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21752, d52706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d52706 q = 1) (hb : d196418 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d196418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d196418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro46850 (p : Pattern) (ha : d13024 p = 1) (hb : d69107 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d1094 q = 1) (hb : d52675 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1094, d52675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41 q ha hb
    | true =>
      simp only [d1094, d52675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro148 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1095 q = 1) (hb : d52676 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1095, d52676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1095, d52676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d51870 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d9452 q = 1) (hb : d69102 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d9452, d69102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7946 q ha hb
    | true =>
      simp only [d9452, d69102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9453 q = 1) (hb : d69103 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d9453, d69103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9453, d69103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d9795 q = 1) (hb : d69104 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d9795, d69104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9795, d69104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d133 q = 1) (hb : d51984 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d133, d51984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18 q ha hb
    | true =>
      simp only [d133, d51984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d134 q = 1) (hb : d51985 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d134, d51985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d134, d51985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d51872 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d9796 q = 1) (hb : d51986 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d9796, d51986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d9796, d51986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d9797 q = 1) (hb : d69105 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d9797, d69105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9797, d69105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d9798 q = 1) (hb : d69106 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d9798, d69106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d9798, d69106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d52700 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d13024 q = 1) (hb : d69107 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d13024, d69107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d13024, d69107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h14 p ha hb
theorem andIntro46851 (p : Pattern) (ha : d69112 p = 1) (hb : d196419 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d69112 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d13025 q = 1) (hb : d69108 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13025, d69108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46850 q ha hb
    | true =>
      simp only [d13025, d69108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13026 q = 1) (hb : d69109 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13026, d69109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13026, d69109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d13027 q = 1) (hb : d69110 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13027, d69110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d13027, d69110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13028 q = 1) (hb : d69111 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13028, d69111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13028, d69111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d21760 q = 1) (hb : d69112 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d21760, d69112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21760, d69112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d69112 q = 1) (hb : d196419 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d196419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d196419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  exact h7 p ha hb
theorem andIntro46852 (p : Pattern) (ha : d195626 p = 1) (hb : d196430 p = 1) : d197392 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d195622 q = 1) (hb : d196420 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d195622, d196420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46849 q ha hb
    | true =>
      simp only [d195622, d196420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46851 q ha hb
  have h2 (q : Pattern) (ha : d195623 q = 1) (hb : d196421 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d195623, d196421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195623, d196421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d195624 q = 1) (hb : d196422 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d195624, d196422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195624, d196422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d195624 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d195624 q = 1) (hb : d196423 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d196423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d196423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d1 q = 1) (hb : d196428 q = 1) : d196428 q = 1 := by
    exact hb
  have h7 (q : Pattern) (ha : d195625 q = 1) (hb : d196429 q = 1) : d197391 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d195625, d196429, d197391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d195625, d196429, d197391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d195626 q = 1) (hb : d196430 q = 1) : d197392 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d195626, d196430, d197392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d195626, d196430, d197392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro46853 (p : Pattern) (ha : d195632 p = 1) (hb : d196440 p = 1) : d197398 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d195627 q = 1) (hb : d196431 q = 1) : d197393 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d195627, d196431, d197393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46852 q ha hb
    | true =>
      simp only [d195627, d196431, d197393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d195628 q = 1) (hb : d196432 q = 1) : d197394 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d195628, d196432, d197394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195628, d196432, d197394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1 q = 1) (hb : d196436 q = 1) : d196436 q = 1 := by
    exact hb
  have h4 (q : Pattern) (ha : d195629 q = 1) (hb : d196437 q = 1) : d197395 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d195629, d196437, d197395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d195629, d196437, d197395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d195630 q = 1) (hb : d196438 q = 1) : d197396 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d195630, d196438, d197396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d195630, d196438, d197396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d195631 q = 1) (hb : d196439 q = 1) : d197397 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d195631, d196439, d197397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d195631, d196439, d197397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d195632 q = 1) (hb : d196440 q = 1) : d197398 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d195632, d196440, d197398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195632, d196440, d197398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro46854 (p : Pattern) (ha : d195638 p = 1) (hb : d196450 p = 1) : d197404 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d196444 q = 1) : d196444 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d195633 q = 1) (hb : d196445 q = 1) : d197399 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195633, d196445, d197399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46853 q ha hb
    | true =>
      simp only [d195633, d196445, d197399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d195634 q = 1) (hb : d196446 q = 1) : d197400 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d195634, d196446, d197400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195634, d196446, d197400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d195635 q = 1) (hb : d196447 q = 1) : d197401 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d195635, d196447, d197401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d195635, d196447, d197401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d195636 q = 1) (hb : d196448 q = 1) : d197402 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d195636, d196448, d197402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195636, d196448, d197402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d195637 q = 1) (hb : d196449 q = 1) : d197403 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d195637, d196449, d197403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195637, d196449, d197403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d195638 q = 1) (hb : d196450 q = 1) : d197404 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d195638, d196450, d197404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195638, d196450, d197404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro46855 (p : Pattern) (ha : d195641 p = 1) (hb : d196453 p = 1) : d197407 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d195627 q = 1) (hb : d196431 q = 1) : d197393 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d195627, d196431, d197393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46852 q ha hb
    | true =>
      simp only [d195627, d196431, d197393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d195628 q = 1) (hb : d196432 q = 1) : d197394 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d195628, d196432, d197394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195628, d196432, d197394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1 q = 1) (hb : d196436 q = 1) : d196436 q = 1 := by
    exact hb
  have h4 (q : Pattern) (ha : d195629 q = 1) (hb : d196437 q = 1) : d197395 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d195629, d196437, d197395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d195629, d196437, d197395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d195630 q = 1) (hb : d196438 q = 1) : d197396 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d195630, d196438, d197396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d195630, d196438, d197396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d195631 q = 1) (hb : d196439 q = 1) : d197397 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d195631, d196439, d197397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d195631, d196439, d197397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d195641 q = 1) (hb : d196453 q = 1) : d197407 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d195641, d196453, d197407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d195641, d196453, d197407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro46856 (p : Pattern) (ha : d195647 p = 1) (hb : d196460 p = 1) : d197413 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d196444 q = 1) : d196444 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d195633 q = 1) (hb : d196445 q = 1) : d197399 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195633, d196445, d197399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46853 q ha hb
    | true =>
      simp only [d195633, d196445, d197399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d195634 q = 1) (hb : d196446 q = 1) : d197400 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d195634, d196446, d197400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195634, d196446, d197400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d195635 q = 1) (hb : d196447 q = 1) : d197401 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d195635, d196447, d197401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d195635, d196447, d197401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d195636 q = 1) (hb : d196448 q = 1) : d197402 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d195636, d196448, d197402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195636, d196448, d197402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d195637 q = 1) (hb : d196449 q = 1) : d197403 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d195637, d196449, d197403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195637, d196449, d197403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1 q = 1) (hb : d196454 q = 1) : d196454 q = 1 := by
    exact hb
  have h8 (q : Pattern) (ha : d195642 q = 1) (hb : d196455 q = 1) : d197408 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195642, d196455, d197408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46855 q ha hb
    | true =>
      simp only [d195642, d196455, d197408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d195643 q = 1) (hb : d196456 q = 1) : d197409 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d195643, d196456, d197409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195643, d196456, d197409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d195644 q = 1) (hb : d196457 q = 1) : d197410 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d195644, d196457, d197410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d195644, d196457, d197410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d195645 q = 1) (hb : d196458 q = 1) : d197411 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d195645, d196458, d197411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195645, d196458, d197411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d195646 q = 1) (hb : d196459 q = 1) : d197412 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d195646, d196459, d197412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195646, d196459, d197412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d195647 q = 1) (hb : d196460 q = 1) : d197413 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d195647, d196460, d197413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d195647, d196460, d197413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro46857 (p : Pattern) (ha : d195626 p = 1) (hb : d196501 p = 1) : d197436 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d195622 q = 1) (hb : d196420 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d195622, d196420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46849 q ha hb
    | true =>
      simp only [d195622, d196420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46851 q ha hb
  have h2 (q : Pattern) (ha : d195623 q = 1) (hb : d196421 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d195623, d196421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195623, d196421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d195624 q = 1) (hb : d196422 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d195624, d196422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195624, d196422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d195624 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d195624 q = 1) (hb : d196423 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d196423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d196423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d1 q = 1) (hb : d196499 q = 1) : d196499 q = 1 := by
    exact hb
  have h7 (q : Pattern) (ha : d195625 q = 1) (hb : d196500 q = 1) : d197435 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d195625, d196500, d197435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d195625, d196500, d197435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d195626 q = 1) (hb : d196501 q = 1) : d197436 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d195626, d196501, d197436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d195626, d196501, d197436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro46858 (p : Pattern) (ha : d195632 p = 1) (hb : d196507 p = 1) : d197442 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d195627 q = 1) (hb : d196502 q = 1) : d197437 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d195627, d196502, d197437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46857 q ha hb
    | true =>
      simp only [d195627, d196502, d197437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d195628 q = 1) (hb : d196503 q = 1) : d197438 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d195628, d196503, d197438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195628, d196503, d197438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d195629 q = 1) (hb : d196504 q = 1) : d197439 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d195629, d196504, d197439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d195629, d196504, d197439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d195630 q = 1) (hb : d196505 q = 1) : d197440 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d195630, d196505, d197440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d195630, d196505, d197440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d195631 q = 1) (hb : d196506 q = 1) : d197441 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d195631, d196506, d197441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d195631, d196506, d197441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d195632 q = 1) (hb : d196507 q = 1) : d197442 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d195632, d196507, d197442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195632, d196507, d197442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro46859 (p : Pattern) (ha : d195652 p = 1) (hb : d196465 p = 1) : d197418 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d195627 q = 1) (hb : d196431 q = 1) : d197393 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d195627, d196431, d197393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46852 q ha hb
    | true =>
      simp only [d195627, d196431, d197393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d195628 q = 1) (hb : d196432 q = 1) : d197394 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d195628, d196432, d197394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195628, d196432, d197394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1 q = 1) (hb : d196436 q = 1) : d196436 q = 1 := by
    exact hb
  have h4 (q : Pattern) (ha : d195629 q = 1) (hb : d196437 q = 1) : d197395 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d195629, d196437, d197395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d195629, d196437, d197395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d195630 q = 1) (hb : d196438 q = 1) : d197396 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d195630, d196438, d197396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d195630, d196438, d197396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d195651 q = 1) (hb : d196464 q = 1) : d197417 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d195651, d196464, d197417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195651, d196464, d197417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d195652 q = 1) (hb : d196465 q = 1) : d197418 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d195652, d196465, d197418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195652, d196465, d197418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro46860 (p : Pattern) (ha : d195659 p = 1) (hb : d196474 p = 1) : d197425 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d195627 q = 1) (hb : d196431 q = 1) : d197393 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d195627, d196431, d197393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46852 q ha hb
    | true =>
      simp only [d195627, d196431, d197393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d195628 q = 1) (hb : d196432 q = 1) : d197394 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d195628, d196432, d197394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195628, d196432, d197394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1 q = 1) (hb : d196436 q = 1) : d196436 q = 1 := by
    exact hb
  have h4 (q : Pattern) (ha : d195629 q = 1) (hb : d196437 q = 1) : d197395 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d195629, d196437, d197395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d195629, d196437, d197395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d195657 q = 1) (hb : d196472 q = 1) : d197423 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d195657, d196472, d197423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195657, d196472, d197423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d195658 q = 1) (hb : d196473 q = 1) : d197424 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d195658, d196473, d197424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d195658, d196473, d197424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d195659 q = 1) (hb : d196474 q = 1) : d197425 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d195659, d196474, d197425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195659, d196474, d197425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro46861 (p : Pattern) (ha : d21840 p = 1) (hb : d52680 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d822 q = 1) (hb : d52499 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d822, d52499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro120 q ha hb
    | true =>
      simp only [d822, d52499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d823 q = 1) (hb : d52500 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d823, d52500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d823, d52500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52670 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d9759 q = 1) (hb : d52671 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d9759, d52671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9759, d52671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d52507 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d9760 q = 1) (hb : d52672 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d9760, d52672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9760, d52672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d9761 q = 1) (hb : d52673 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d9761, d52673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9761, d52673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52679 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d21840 q = 1) (hb : d52680 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d21840, d52680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21840, d52680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro46862 (p : Pattern) (ha : d52695 p = 1) (hb : d196481 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52695 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d21841 q = 1) (hb : d52681 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21841, d52681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46861 q ha hb
    | true =>
      simp only [d21841, d52681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21842 q = 1) (hb : d52682 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21842, d52682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21842, d52682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d21843 q = 1) (hb : d52683 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d21843, d52683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d21843, d52683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21844 q = 1) (hb : d52684 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d21844, d52684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21844, d52684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d21748 q = 1) (hb : d52691 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21748, d52691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46848 q ha hb
    | true =>
      simp only [d21748, d52691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d21749 q = 1) (hb : d52692 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21749, d52692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21749, d52692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d21750 q = 1) (hb : d52693 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d21750, d52693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d21750, d52693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d21751 q = 1) (hb : d52694 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d21751, d52694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d21751, d52694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d21845 q = 1) (hb : d52695 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d21845, d52695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21845, d52695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d52695 q = 1) (hb : d196481 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d196481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d196481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro46863 (p : Pattern) (ha : d21747 p = 1) (hb : d101334 p = 1) : d0 p = 1 := by
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
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d101292 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d9581 q = 1) (hb : d101293 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d9581, d101293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23289 q ha hb
    | true =>
      simp only [d9581, d101293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9582 q = 1) (hb : d101294 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d9582, d101294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9582, d101294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d9768 q = 1) (hb : d101331 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d9768, d101331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9768, d101331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d9769 q = 1) (hb : d101332 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d9769, d101332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9769, d101332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d9770 q = 1) (hb : d101333 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d9770, d101333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d9770, d101333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d101297 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d21747 q = 1) (hb : d101334 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d21747, d101334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d21747, d101334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro46864 (p : Pattern) (ha : d113359 p = 1) (hb : d196418 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d113359 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d21748 q = 1) (hb : d101335 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21748, d101335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46863 q ha hb
    | true =>
      simp only [d21748, d101335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21749 q = 1) (hb : d101337 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21749, d101337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21749, d101337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d21750 q = 1) (hb : d113352 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d21750, d113352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d21750, d113352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21751 q = 1) (hb : d113353 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d21751, d113353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21751, d113353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d13025 q = 1) (hb : d113355 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13025, d113355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29765 q ha hb
    | true =>
      simp only [d13025, d113355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d13026 q = 1) (hb : d113356 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13026, d113356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13026, d113356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d13027 q = 1) (hb : d113357 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13027, d113357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d13027, d113357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d13028 q = 1) (hb : d113358 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13028, d113358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d13028, d113358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d21752 q = 1) (hb : d113359 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d21752, d113359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21752, d113359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d113359 q = 1) (hb : d196418 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d196418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d196418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro46865 (p : Pattern) (ha : d195667 p = 1) (hb : d196487 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d195663 q = 1) (hb : d196482 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d195663, d196482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46862 q ha hb
    | true =>
      simp only [d195663, d196482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46864 q ha hb
  have h2 (q : Pattern) (ha : d195664 q = 1) (hb : d196483 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d195664, d196483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195664, d196483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d195665 q = 1) (hb : d196484 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d195665, d196484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195665, d196484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d195665 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d195665 q = 1) (hb : d196485 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d196485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d196485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d195622 q = 1) (hb : d196420 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d195622, d196420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46849 q ha hb
    | true =>
      simp only [d195622, d196420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46851 q ha hb
  have h7 (q : Pattern) (ha : d195623 q = 1) (hb : d196421 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d195623, d196421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195623, d196421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d195624 q = 1) (hb : d196422 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d195624, d196422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195624, d196422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d195624 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d195624 q = 1) (hb : d196423 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d196423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d196423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d195666 q = 1) (hb : d196486 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d195666, d196486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d195666, d196486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d195667 q = 1) (hb : d196487 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d195667, d196487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d195667, d196487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h12 p ha hb
theorem andIntro46866 (p : Pattern) (ha : d195673 p = 1) (hb : d196493 p = 1) : d197432 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d195668 q = 1) (hb : d196488 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d195668, d196488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46865 q ha hb
    | true =>
      simp only [d195668, d196488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d195669 q = 1) (hb : d196489 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d195669, d196489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195669, d196489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d195627 q = 1) (hb : d196431 q = 1) : d197393 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d195627, d196431, d197393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46852 q ha hb
    | true =>
      simp only [d195627, d196431, d197393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d195628 q = 1) (hb : d196432 q = 1) : d197394 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d195628, d196432, d197394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195628, d196432, d197394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d195670 q = 1) (hb : d196490 q = 1) : d197429 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d195670, d196490, d197429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d195670, d196490, d197429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d195671 q = 1) (hb : d196491 q = 1) : d197430 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d195671, d196491, d197430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d195671, d196491, d197430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d195672 q = 1) (hb : d196492 q = 1) : d197431 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d195672, d196492, d197431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d195672, d196492, d197431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d195673 q = 1) (hb : d196493 q = 1) : d197432 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d195673, d196493, d197432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195673, d196493, d197432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro46867 (p : Pattern) (ha : d195680 p = 1) (hb : d196513 p = 1) : d197448 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d196467 q = 1) : d196467 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d195653 q = 1) (hb : d196468 q = 1) : d197419 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195653, d196468, d197419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46859 q ha hb
    | true =>
      simp only [d195653, d196468, d197419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d195654 q = 1) (hb : d196469 q = 1) : d197420 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d195654, d196469, d197420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195654, d196469, d197420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d195655 q = 1) (hb : d196470 q = 1) : d197421 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d195655, d196470, d197421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d195655, d196470, d197421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d195656 q = 1) (hb : d196471 q = 1) : d197422 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d195656, d196471, d197422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195656, d196471, d197422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1 q = 1) (hb : d196477 q = 1) : d196477 q = 1 := by
    exact hb
  have h7 (q : Pattern) (ha : d195660 q = 1) (hb : d196478 q = 1) : d197426 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195660, d196478, d197426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46860 q ha hb
    | true =>
      simp only [d195660, d196478, d197426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d195661 q = 1) (hb : d196479 q = 1) : d197427 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d195661, d196479, d197427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195661, d196479, d197427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d195662 q = 1) (hb : d196480 q = 1) : d197428 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d195662, d196480, d197428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d195662, d196480, d197428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d195674 q = 1) (hb : d196494 q = 1) : d197433 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195674, d196494, d197433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46866 q ha hb
    | true =>
      simp only [d195674, d196494, d197433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46853 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d195633 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d195675 q = 1) (hb : d196495 q = 1) : d197434 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d195675, d196495, d197434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d195675, d196495, d197434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d195633 q = 1) (hb : d196508 q = 1) : d197443 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195633, d196508, d197443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46858 q ha hb
    | true =>
      simp only [d195633, d196508, d197443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d195676 q = 1) (hb : d196509 q = 1) : d197444 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d195676, d196509, d197444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d195676, d196509, d197444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d195677 q = 1) (hb : d196510 q = 1) : d197445 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d195677, d196510, d197445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d195677, d196510, d197445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d195678 q = 1) (hb : d196511 q = 1) : d197446 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d195678, d196511, d197446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d195678, d196511, d197446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d195679 q = 1) (hb : d196512 q = 1) : d197447 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d195679, d196512, d197447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d195679, d196512, d197447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d195680 q = 1) (hb : d196513 q = 1) : d197448 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d195680, d196513, d197448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195680, d196513, d197448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro46868 (p : Pattern) (ha : d195641 p = 1) (hb : d196528 p = 1) : d197461 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d195627 q = 1) (hb : d196502 q = 1) : d197437 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d195627, d196502, d197437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46857 q ha hb
    | true =>
      simp only [d195627, d196502, d197437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d195628 q = 1) (hb : d196503 q = 1) : d197438 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d195628, d196503, d197438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195628, d196503, d197438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d195629 q = 1) (hb : d196504 q = 1) : d197439 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d195629, d196504, d197439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d195629, d196504, d197439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d195630 q = 1) (hb : d196505 q = 1) : d197440 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d195630, d196505, d197440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d195630, d196505, d197440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d195631 q = 1) (hb : d196506 q = 1) : d197441 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d195631, d196506, d197441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d195631, d196506, d197441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d195641 q = 1) (hb : d196528 q = 1) : d197461 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d195641, d196528, d197461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d195641, d196528, d197461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro46869 (p : Pattern) (ha : d195681 p = 1) (hb : d196514 p = 1) : d197449 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d195627 q = 1) (hb : d196431 q = 1) : d197393 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d195627, d196431, d197393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46852 q ha hb
    | true =>
      simp only [d195627, d196431, d197393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d195628 q = 1) (hb : d196432 q = 1) : d197394 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d195628, d196432, d197394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195628, d196432, d197394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1 q = 1) (hb : d196436 q = 1) : d196436 q = 1 := by
    exact hb
  have h4 (q : Pattern) (ha : d195629 q = 1) (hb : d196437 q = 1) : d197395 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d195629, d196437, d197395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d195629, d196437, d197395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d195630 q = 1) (hb : d196438 q = 1) : d197396 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d195630, d196438, d197396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d195630, d196438, d197396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d195651 q = 1) (hb : d196464 q = 1) : d197417 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d195651, d196464, d197417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195651, d196464, d197417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d195681 q = 1) (hb : d196514 q = 1) : d197449 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d195681, d196514, d197449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d195681, d196514, d197449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro46870 (p : Pattern) (ha : d195686 p = 1) (hb : d196520 p = 1) : d197454 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d195627 q = 1) (hb : d196431 q = 1) : d197393 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d195627, d196431, d197393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46852 q ha hb
    | true =>
      simp only [d195627, d196431, d197393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d195628 q = 1) (hb : d196432 q = 1) : d197394 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d195628, d196432, d197394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195628, d196432, d197394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1 q = 1) (hb : d196436 q = 1) : d196436 q = 1 := by
    exact hb
  have h4 (q : Pattern) (ha : d195629 q = 1) (hb : d196437 q = 1) : d197395 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d195629, d196437, d197395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d195629, d196437, d197395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d195657 q = 1) (hb : d196472 q = 1) : d197423 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d195657, d196472, d197423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195657, d196472, d197423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d195658 q = 1) (hb : d196473 q = 1) : d197424 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d195658, d196473, d197424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d195658, d196473, d197424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d195686 q = 1) (hb : d196520 q = 1) : d197454 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d195686, d196520, d197454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d195686, d196520, d197454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro46871 (p : Pattern) (ha : d195690 p = 1) (hb : d196525 p = 1) : d197458 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d195668 q = 1) (hb : d196488 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d195668, d196488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46865 q ha hb
    | true =>
      simp only [d195668, d196488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d195669 q = 1) (hb : d196489 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d195669, d196489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195669, d196489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d195627 q = 1) (hb : d196431 q = 1) : d197393 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d195627, d196431, d197393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46852 q ha hb
    | true =>
      simp only [d195627, d196431, d197393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d195628 q = 1) (hb : d196432 q = 1) : d197394 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d195628, d196432, d197394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195628, d196432, d197394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d195670 q = 1) (hb : d196490 q = 1) : d197429 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d195670, d196490, d197429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d195670, d196490, d197429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d195671 q = 1) (hb : d196491 q = 1) : d197430 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d195671, d196491, d197430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d195671, d196491, d197430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d195672 q = 1) (hb : d196492 q = 1) : d197431 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d195672, d196492, d197431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d195672, d196492, d197431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d195690 q = 1) (hb : d196525 q = 1) : d197458 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d195690, d196525, d197458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d195690, d196525, d197458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro46872 (p : Pattern) (ha : d195697 p = 1) (hb : d196534 p = 1) : d197467 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d196467 q = 1) : d196467 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d195653 q = 1) (hb : d196468 q = 1) : d197419 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195653, d196468, d197419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46859 q ha hb
    | true =>
      simp only [d195653, d196468, d197419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d195654 q = 1) (hb : d196469 q = 1) : d197420 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d195654, d196469, d197420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195654, d196469, d197420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d195655 q = 1) (hb : d196470 q = 1) : d197421 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d195655, d196470, d197421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d195655, d196470, d197421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d195656 q = 1) (hb : d196471 q = 1) : d197422 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d195656, d196471, d197422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195656, d196471, d197422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1 q = 1) (hb : d196477 q = 1) : d196477 q = 1 := by
    exact hb
  have h7 (q : Pattern) (ha : d195660 q = 1) (hb : d196478 q = 1) : d197426 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195660, d196478, d197426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46860 q ha hb
    | true =>
      simp only [d195660, d196478, d197426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d195661 q = 1) (hb : d196479 q = 1) : d197427 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d195661, d196479, d197427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195661, d196479, d197427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d195662 q = 1) (hb : d196480 q = 1) : d197428 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d195662, d196480, d197428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d195662, d196480, d197428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d195674 q = 1) (hb : d196494 q = 1) : d197433 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195674, d196494, d197433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46866 q ha hb
    | true =>
      simp only [d195674, d196494, d197433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46853 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d195633 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d195675 q = 1) (hb : d196495 q = 1) : d197434 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d195675, d196495, d197434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d195675, d196495, d197434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d195633 q = 1) (hb : d196508 q = 1) : d197443 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195633, d196508, d197443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46858 q ha hb
    | true =>
      simp only [d195633, d196508, d197443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d195676 q = 1) (hb : d196509 q = 1) : d197444 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d195676, d196509, d197444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d195676, d196509, d197444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d195677 q = 1) (hb : d196510 q = 1) : d197445 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d195677, d196510, d197445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d195677, d196510, d197445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d195678 q = 1) (hb : d196511 q = 1) : d197446 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d195678, d196511, d197446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d195678, d196511, d197446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d195679 q = 1) (hb : d196512 q = 1) : d197447 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d195679, d196512, d197447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d195679, d196512, d197447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d1 q = 1) (hb : d196515 q = 1) : d196515 q = 1 := by
    exact hb
  have h19 (q : Pattern) (ha : d195682 q = 1) (hb : d196516 q = 1) : d197450 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195682, d196516, d197450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46869 q ha hb
    | true =>
      simp only [d195682, d196516, d197450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d195683 q = 1) (hb : d196517 q = 1) : d197451 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d195683, d196517, d197451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195683, d196517, d197451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d195684 q = 1) (hb : d196518 q = 1) : d197452 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d195684, d196518, d197452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d195684, d196518, d197452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d195685 q = 1) (hb : d196519 q = 1) : d197453 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d195685, d196519, d197453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195685, d196519, d197453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d1 q = 1) (hb : d196521 q = 1) : d196521 q = 1 := by
    exact hb
  have h24 (q : Pattern) (ha : d195687 q = 1) (hb : d196522 q = 1) : d197455 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195687, d196522, d197455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46870 q ha hb
    | true =>
      simp only [d195687, d196522, d197455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d195688 q = 1) (hb : d196523 q = 1) : d197456 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d195688, d196523, d197456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195688, d196523, d197456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
  have h26 (q : Pattern) (ha : d195689 q = 1) (hb : d196524 q = 1) : d197457 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d195689, d196524, d197457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d195689, d196524, d197457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d195691 q = 1) (hb : d196526 q = 1) : d197459 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195691, d196526, d197459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46871 q ha hb
    | true =>
      simp only [d195691, d196526, d197459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46855 q ha hb
  have h28 (q : Pattern) (ha : d0 q = 1) (hb : d195642 q = 1) : d0 q = 1 := by
    exact ha
  have h29 (q : Pattern) (ha : d195692 q = 1) (hb : d196527 q = 1) : d197460 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d195692, d196527, d197460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
    | true =>
      simp only [d195692, d196527, d197460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q hb ha
  have h30 (q : Pattern) (ha : d195642 q = 1) (hb : d196529 q = 1) : d197462 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195642, d196529, d197462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46868 q ha hb
    | true =>
      simp only [d195642, d196529, d197462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h31 (q : Pattern) (ha : d195693 q = 1) (hb : d196530 q = 1) : d197463 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d195693, d196530, d197463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
    | true =>
      simp only [d195693, d196530, d197463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h32 (q : Pattern) (ha : d195694 q = 1) (hb : d196531 q = 1) : d197464 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d195694, d196531, d197464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
    | true =>
      simp only [d195694, d196531, d197464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
  have h33 (q : Pattern) (ha : d195695 q = 1) (hb : d196532 q = 1) : d197465 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d195695, d196532, d197465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d195695, d196532, d197465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h32 q ha hb
  have h34 (q : Pattern) (ha : d195696 q = 1) (hb : d196533 q = 1) : d197466 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d195696, d196533, d197466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d195696, d196533, d197466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h33 q ha hb
  have h35 (q : Pattern) (ha : d195697 q = 1) (hb : d196534 q = 1) : d197467 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d195697, d196534, d197467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d195697, d196534, d197467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h34 q ha hb
  exact h35 p ha hb
theorem andIntro46873 (p : Pattern) (ha : d195699 p = 1) (hb : d196541 p = 1) : d197469 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d196444 q = 1) : d196444 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d195633 q = 1) (hb : d196445 q = 1) : d197399 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195633, d196445, d197399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46853 q ha hb
    | true =>
      simp only [d195633, d196445, d197399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d195634 q = 1) (hb : d196446 q = 1) : d197400 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d195634, d196446, d197400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195634, d196446, d197400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d195635 q = 1) (hb : d196447 q = 1) : d197401 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d195635, d196447, d197401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d195635, d196447, d197401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d195636 q = 1) (hb : d196448 q = 1) : d197402 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d195636, d196448, d197402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195636, d196448, d197402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d195637 q = 1) (hb : d196449 q = 1) : d197403 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d195637, d196449, d197403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195637, d196449, d197403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1 q = 1) (hb : d196540 q = 1) : d196540 q = 1 := by
    exact hb
  have h8 (q : Pattern) (ha : d195699 q = 1) (hb : d196541 q = 1) : d197469 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d195699, d196541, d197469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d195699, d196541, d197469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro46874 (p : Pattern) (ha : d195706 p = 1) (hb : d196554 p = 1) : d197476 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d195691 q = 1) (hb : d196526 q = 1) : d197459 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195691, d196526, d197459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46871 q ha hb
    | true =>
      simp only [d195691, d196526, d197459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46855 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d195642 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d195692 q = 1) (hb : d196527 q = 1) : d197460 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d195692, d196527, d197460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d195692, d196527, d197460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d195642 q = 1) (hb : d196529 q = 1) : d197462 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195642, d196529, d197462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46868 q ha hb
    | true =>
      simp only [d195642, d196529, d197462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d195693 q = 1) (hb : d196530 q = 1) : d197463 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d195693, d196530, d197463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d195693, d196530, d197463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d195694 q = 1) (hb : d196531 q = 1) : d197464 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d195694, d196531, d197464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d195694, d196531, d197464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d195704 q = 1) (hb : d196552 q = 1) : d197474 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d195704, d196552, d197474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195704, d196552, d197474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d195705 q = 1) (hb : d196553 q = 1) : d197475 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d195705, d196553, d197475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195705, d196553, d197475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d195706 q = 1) (hb : d196554 q = 1) : d197476 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d195706, d196554, d197476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195706, d196554, d197476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro46875 (p : Pattern) (ha : d52877 p = 1) (hb : d196562 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52877 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d22033 q = 1) (hb : d52868 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22033, d52868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d22033, d52868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46861 q ha hb
  have h3 (q : Pattern) (ha : d21841 q = 1) (hb : d52681 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21841, d52681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46861 q ha hb
    | true =>
      simp only [d21841, d52681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d22034 q = 1) (hb : d52869 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22034, d52869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22034, d52869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21842 q = 1) (hb : d52682 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21842, d52682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21842, d52682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d22035 q = 1) (hb : d52870 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d22035, d52870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d22035, d52870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d22036 q = 1) (hb : d52871 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d22036, d52871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22036, d52871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d22037 q = 1) (hb : d52873 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22037, d52873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d22037, d52873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46848 q ha hb
  have h9 (q : Pattern) (ha : d21748 q = 1) (hb : d52691 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21748, d52691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46848 q ha hb
    | true =>
      simp only [d21748, d52691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d22038 q = 1) (hb : d52874 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22038, d52874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d22038, d52874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d21749 q = 1) (hb : d52692 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21749, d52692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d21749, d52692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h12 (q : Pattern) (ha : d22039 q = 1) (hb : d52875 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d22039, d52875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d22039, d52875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d22040 q = 1) (hb : d52876 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d22040, d52876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d22040, d52876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h14 (q : Pattern) (ha : d22041 q = 1) (hb : d52877 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22041, d52877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22041, d52877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d52877 q = 1) (hb : d196562 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d196562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d196562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  exact h15 p ha hb
theorem andIntro46876 (p : Pattern) (ha : d52883 p = 1) (hb : d196563 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52883 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d22037 q = 1) (hb : d52873 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22037, d52873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d22037, d52873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46848 q ha hb
  have h3 (q : Pattern) (ha : d21748 q = 1) (hb : d52691 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21748, d52691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46848 q ha hb
    | true =>
      simp only [d21748, d52691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d22038 q = 1) (hb : d52874 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22038, d52874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22038, d52874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21749 q = 1) (hb : d52692 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21749, d52692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21749, d52692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d22039 q = 1) (hb : d52875 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d22039, d52875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d22039, d52875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d22040 q = 1) (hb : d52876 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d22040, d52876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22040, d52876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d13164 q = 1) (hb : d52879 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13164, d52879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d13164, d52879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46847 q ha hb
  have h9 (q : Pattern) (ha : d13025 q = 1) (hb : d52702 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13025, d52702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46847 q ha hb
    | true =>
      simp only [d13025, d52702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d13165 q = 1) (hb : d52880 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13165, d52880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d13165, d52880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d13026 q = 1) (hb : d52703 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13026, d52703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d13026, d52703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h12 (q : Pattern) (ha : d13166 q = 1) (hb : d52881 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13166, d52881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d13166, d52881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d13167 q = 1) (hb : d52882 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13167, d52882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d13167, d52882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h14 (q : Pattern) (ha : d22048 q = 1) (hb : d52883 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22048, d52883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22048, d52883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d52883 q = 1) (hb : d196563 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d196563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d196563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  exact h15 p ha hb
theorem andIntro46877 (p : Pattern) (ha : d76094 p = 1) (hb : d196568 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d76094 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d13164 q = 1) (hb : d76090 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13164, d76090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d13164, d76090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46850 q ha hb
  have h3 (q : Pattern) (ha : d13025 q = 1) (hb : d69108 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13025, d69108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46850 q ha hb
    | true =>
      simp only [d13025, d69108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d13165 q = 1) (hb : d76091 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13165, d76091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13165, d76091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13026 q = 1) (hb : d69109 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13026, d69109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13026, d69109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d13166 q = 1) (hb : d76092 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13166, d76092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13166, d76092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d13167 q = 1) (hb : d76093 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13167, d76093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13167, d76093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d22058 q = 1) (hb : d76094 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22058, d76094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22058, d76094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h9 (q : Pattern) (ha : d76094 q = 1) (hb : d196568 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d196568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d196568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  exact h9 p ha hb
theorem andIntro46878 (p : Pattern) (ha : d113460 p = 1) (hb : d196563 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d113460 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d22037 q = 1) (hb : d113452 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22037, d113452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d22037, d113452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46863 q ha hb
  have h3 (q : Pattern) (ha : d21748 q = 1) (hb : d101335 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21748, d101335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46863 q ha hb
    | true =>
      simp only [d21748, d101335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d22038 q = 1) (hb : d113453 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22038, d113453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22038, d113453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21749 q = 1) (hb : d101337 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21749, d101337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21749, d101337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d22039 q = 1) (hb : d113454 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d22039, d113454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d22039, d113454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d22040 q = 1) (hb : d113455 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d22040, d113455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22040, d113455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d13164 q = 1) (hb : d113456 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13164, d113456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d13164, d113456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29765 q ha hb
  have h9 (q : Pattern) (ha : d13025 q = 1) (hb : d113355 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13025, d113355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29765 q ha hb
    | true =>
      simp only [d13025, d113355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d13165 q = 1) (hb : d113457 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13165, d113457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d13165, d113457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d13026 q = 1) (hb : d113356 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13026, d113356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d13026, d113356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h12 (q : Pattern) (ha : d13166 q = 1) (hb : d113458 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13166, d113458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d13166, d113458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d13167 q = 1) (hb : d113459 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13167, d113459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d13167, d113459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h14 (q : Pattern) (ha : d22048 q = 1) (hb : d113460 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22048, d113460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22048, d113460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d113460 q = 1) (hb : d196563 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d196563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d196563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  exact h15 p ha hb
theorem andIntro46879 (p : Pattern) (ha : d195719 p = 1) (hb : d196574 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d195712 q = 1) (hb : d196564 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d195712, d196564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46875 q ha hb
    | true =>
      simp only [d195712, d196564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46878 q ha hb
  have h2 (q : Pattern) (ha : d195713 q = 1) (hb : d196565 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d195713, d196565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195713, d196565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d195714 q = 1) (hb : d196566 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d195714, d196566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195714, d196566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d195714 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d195714 q = 1) (hb : d196567 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d196567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d196567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d195715 q = 1) (hb : d196569 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d195715, d196569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46876 q ha hb
    | true =>
      simp only [d195715, d196569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46877 q ha hb
  have h7 (q : Pattern) (ha : d195716 q = 1) (hb : d196570 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d195716, d196570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195716, d196570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d195717 q = 1) (hb : d196571 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d195717, d196571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195717, d196571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d195717 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d195717 q = 1) (hb : d196572 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d196572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d196572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d195718 q = 1) (hb : d196573 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d195718, d196573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d195718, d196573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d195719 q = 1) (hb : d196574 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d195719, d196574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d195719, d196574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h12 p ha hb
theorem andIntro46880 (p : Pattern) (ha : d195723 p = 1) (hb : d196583 p = 1) : d197483 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d195715 q = 1) (hb : d196569 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d195715, d196569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46876 q ha hb
    | true =>
      simp only [d195715, d196569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46877 q ha hb
  have h2 (q : Pattern) (ha : d195716 q = 1) (hb : d196570 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d195716, d196570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195716, d196570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d195717 q = 1) (hb : d196571 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d195717, d196571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195717, d196571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d195717 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d195717 q = 1) (hb : d196572 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d196572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d196572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d1 q = 1) (hb : d196581 q = 1) : d196581 q = 1 := by
    exact hb
  have h7 (q : Pattern) (ha : d195722 q = 1) (hb : d196582 q = 1) : d197482 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d195722, d196582, d197482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d195722, d196582, d197482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d195723 q = 1) (hb : d196583 q = 1) : d197483 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d195723, d196583, d197483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d195723, d196583, d197483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro46881 (p : Pattern) (ha : d195729 p = 1) (hb : d196589 p = 1) : d197489 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d195720 q = 1) (hb : d196575 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d195720, d196575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46879 q ha hb
    | true =>
      simp only [d195720, d196575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d195721 q = 1) (hb : d196576 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d195721, d196576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195721, d196576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d195724 q = 1) (hb : d196584 q = 1) : d197484 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d195724, d196584, d197484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46880 q ha hb
    | true =>
      simp only [d195724, d196584, d197484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d195725 q = 1) (hb : d196585 q = 1) : d197485 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d195725, d196585, d197485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195725, d196585, d197485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d195726 q = 1) (hb : d196586 q = 1) : d197486 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d195726, d196586, d197486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d195726, d196586, d197486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d195727 q = 1) (hb : d196587 q = 1) : d197487 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d195727, d196587, d197487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d195727, d196587, d197487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d195728 q = 1) (hb : d196588 q = 1) : d197488 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d195728, d196588, d197488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d195728, d196588, d197488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d195729 q = 1) (hb : d196589 q = 1) : d197489 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d195729, d196589, d197489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d195729, d196589, d197489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro46882 (p : Pattern) (ha : d195733 p = 1) (hb : d196597 p = 1) : d197493 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d195724 q = 1) (hb : d196584 q = 1) : d197484 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d195724, d196584, d197484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46880 q ha hb
    | true =>
      simp only [d195724, d196584, d197484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d195725 q = 1) (hb : d196585 q = 1) : d197485 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d195725, d196585, d197485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195725, d196585, d197485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1 q = 1) (hb : d196593 q = 1) : d196593 q = 1 := by
    exact hb
  have h4 (q : Pattern) (ha : d195730 q = 1) (hb : d196594 q = 1) : d197490 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d195730, d196594, d197490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d195730, d196594, d197490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d195731 q = 1) (hb : d196595 q = 1) : d197491 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d195731, d196595, d197491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d195731, d196595, d197491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d195732 q = 1) (hb : d196596 q = 1) : d197492 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d195732, d196596, d197492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d195732, d196596, d197492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d195733 q = 1) (hb : d196597 q = 1) : d197493 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d195733, d196597, d197493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d195733, d196597, d197493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro46883 (p : Pattern) (ha : d195723 p = 1) (hb : d196605 p = 1) : d197497 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d195715 q = 1) (hb : d196569 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d195715, d196569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46876 q ha hb
    | true =>
      simp only [d195715, d196569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46877 q ha hb
  have h2 (q : Pattern) (ha : d195716 q = 1) (hb : d196570 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d195716, d196570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195716, d196570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d195717 q = 1) (hb : d196571 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d195717, d196571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195717, d196571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d195717 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d195717 q = 1) (hb : d196572 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d196572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d196572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d1 q = 1) (hb : d196603 q = 1) : d196603 q = 1 := by
    exact hb
  have h7 (q : Pattern) (ha : d195722 q = 1) (hb : d196604 q = 1) : d197496 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d195722, d196604, d197496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d195722, d196604, d197496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d195723 q = 1) (hb : d196605 q = 1) : d197497 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d195723, d196605, d197497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d195723, d196605, d197497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro46884 (p : Pattern) (ha : d195733 p = 1) (hb : d196611 p = 1) : d197503 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d195724 q = 1) (hb : d196606 q = 1) : d197498 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d195724, d196606, d197498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46883 q ha hb
    | true =>
      simp only [d195724, d196606, d197498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d195725 q = 1) (hb : d196607 q = 1) : d197499 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d195725, d196607, d197499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195725, d196607, d197499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d195730 q = 1) (hb : d196608 q = 1) : d197500 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d195730, d196608, d197500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d195730, d196608, d197500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d195731 q = 1) (hb : d196609 q = 1) : d197501 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d195731, d196609, d197501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d195731, d196609, d197501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d195732 q = 1) (hb : d196610 q = 1) : d197502 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d195732, d196610, d197502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d195732, d196610, d197502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d195733 q = 1) (hb : d196611 q = 1) : d197503 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d195733, d196611, d197503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d195733, d196611, d197503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro46885 (p : Pattern) (ha : d195741 p = 1) (hb : d196617 p = 1) : d197509 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d195734 q = 1) (hb : d196598 q = 1) : d197494 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195734, d196598, d197494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46881 q ha hb
    | true =>
      simp only [d195734, d196598, d197494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46882 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d195735 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d195736 q = 1) (hb : d196599 q = 1) : d197495 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d195736, d196599, d197495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d195736, d196599, d197495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d195735 q = 1) (hb : d196612 q = 1) : d197504 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195735, d196612, d197504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46884 q ha hb
    | true =>
      simp only [d195735, d196612, d197504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d195737 q = 1) (hb : d196613 q = 1) : d197505 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d195737, d196613, d197505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d195737, d196613, d197505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d195738 q = 1) (hb : d196614 q = 1) : d197506 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d195738, d196614, d197506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d195738, d196614, d197506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d195739 q = 1) (hb : d196615 q = 1) : d197507 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d195739, d196615, d197507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195739, d196615, d197507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d195740 q = 1) (hb : d196616 q = 1) : d197508 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d195740, d196616, d197508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195740, d196616, d197508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d195741 q = 1) (hb : d196617 q = 1) : d197509 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d195741, d196617, d197509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195741, d196617, d197509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro46886 (p : Pattern) (ha : d195747 p = 1) (hb : d196634 p = 1) : d197515 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d195639 q = 1) (hb : d196451 q = 1) : d197405 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d195639, d196451, d197405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195639, d196451, d197405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46854 q ha hb
  have h2 (q : Pattern) (ha : d195640 q = 1) (hb : d196452 q = 1) : d197406 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d195640, d196452, d197406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d195640, d196452, d197406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d195648 q = 1) (hb : d196461 q = 1) : d197414 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d195648, d196461, d197414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46854 q ha hb
    | true =>
      simp only [d195648, d196461, d197414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46856 q ha hb
  have h4 (q : Pattern) (ha : d195649 q = 1) (hb : d196462 q = 1) : d197415 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d195649, d196462, d197415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d195649, d196462, d197415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d195650 q = 1) (hb : d196463 q = 1) : d197416 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d195650, d196463, d197416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d195650, d196463, d197416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d195698 q = 1) (hb : d196535 q = 1) : d197468 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d195698, d196535, d197468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46867 q ha hb
    | true =>
      simp only [d195698, d196535, d197468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46872 q ha hb
  have h7 (q : Pattern) (ha : d1 q = 1) (hb : d196547 q = 1) : d196547 q = 1 := by
    exact hb
  have h8 (q : Pattern) (ha : d195700 q = 1) (hb : d196548 q = 1) : d197470 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d195700, d196548, d197470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46873 q ha hb
    | true =>
      simp only [d195700, d196548, d197470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d195701 q = 1) (hb : d196549 q = 1) : d197471 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d195701, d196549, d197471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d195701, d196549, d197471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d195702 q = 1) (hb : d196550 q = 1) : d197472 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d195702, d196550, d197472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d195702, d196550, d197472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d195703 q = 1) (hb : d196551 q = 1) : d197473 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d195703, d196551, d197473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d195703, d196551, d197473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d195707 q = 1) (hb : d196555 q = 1) : d197477 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d195707, d196555, d197477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195707, d196555, d197477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46874 q ha hb
  have h13 (q : Pattern) (ha : d1 q = 1) (hb : d196557 q = 1) : d196557 q = 1 := by
    exact hb
  have h14 (q : Pattern) (ha : d195708 q = 1) (hb : d196558 q = 1) : d197478 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d195708, d196558, d197478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d195708, d196558, d197478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d195709 q = 1) (hb : d196559 q = 1) : d197479 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d195709, d196559, d197479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d195709, d196559, d197479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d195710 q = 1) (hb : d196560 q = 1) : d197480 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d195710, d196560, d197480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d195710, d196560, d197480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h17 (q : Pattern) (ha : d195711 q = 1) (hb : d196561 q = 1) : d197481 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d195711, d196561, d197481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d195711, d196561, d197481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d195742 q = 1) (hb : d196618 q = 1) : d197510 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d195742, d196618, d197510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195742, d196618, d197510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46885 q ha hb
  have h19 (q : Pattern) (ha : d1 q = 1) (hb : d196629 q = 1) : d196629 q = 1 := by
    exact hb
  have h20 (q : Pattern) (ha : d195743 q = 1) (hb : d196630 q = 1) : d197511 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d195743, d196630, d197511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d195743, d196630, d197511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d195744 q = 1) (hb : d196631 q = 1) : d197512 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d195744, d196631, d197512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d195744, d196631, d197512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d195745 q = 1) (hb : d196632 q = 1) : d197513 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d195745, d196632, d197513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d195745, d196632, d197513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d195746 q = 1) (hb : d196633 q = 1) : d197514 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d195746, d196633, d197514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d195746, d196633, d197514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d195747 q = 1) (hb : d196634 q = 1) : d197515 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d195747, d196634, d197515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d195747, d196634, d197515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  exact h24 p ha hb
theorem andIntro46887 (p : Pattern) (ha : d195753 p = 1) (hb : d196640 p = 1) : d197521 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d195748 q = 1) (hb : d196635 q = 1) : d197516 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d195748, d196635, d197516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195748, d196635, d197516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46886 q ha hb
  have h2 (q : Pattern) (ha : d195749 q = 1) (hb : d196636 q = 1) : d197517 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d195749, d196636, d197517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195749, d196636, d197517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d195750 q = 1) (hb : d196637 q = 1) : d197518 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d195750, d196637, d197518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195750, d196637, d197518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d195751 q = 1) (hb : d196638 q = 1) : d197519 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d195751, d196638, d197519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195751, d196638, d197519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d195752 q = 1) (hb : d196639 q = 1) : d197520 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d195752, d196639, d197520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195752, d196639, d197520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d195753 q = 1) (hb : d196640 q = 1) : d197521 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d195753, d196640, d197521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195753, d196640, d197521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro46888 (p : Pattern) (ha : d13350 p = 1) (hb : d53022 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d1543 q = 1) (hb : d52984 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1543, d52984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro202 q ha hb
    | true =>
      simp only [d1543, d52984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro203 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1544 q = 1) (hb : d52985 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1544, d52985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1544, d52985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro148 q ha hb
  have h3 (q : Pattern) (ha : d1545 q = 1) (hb : d52986 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1545, d52986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1545, d52986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d53000 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d10057 q = 1) (hb : d53001 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d10057, d53001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35610 q ha hb
    | true =>
      simp only [d10057, d53001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d52696 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d10058 q = 1) (hb : d53002 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d10058, d53002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10058, d53002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d10080 q = 1) (hb : d53003 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d10080, d53003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10080, d53003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d1549 q = 1) (hb : d52990 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1549, d52990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro204 q ha hb
    | true =>
      simp only [d1549, d52990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d1550 q = 1) (hb : d52991 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1550, d52991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d1550, d52991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d53006 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d10081 q = 1) (hb : d53007 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d10081, d53007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d10081, d53007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d10082 q = 1) (hb : d53008 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d10082, d53008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d10082, d53008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d10083 q = 1) (hb : d53009 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d10083, d53009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d10083, d53009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d53021 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d13350 q = 1) (hb : d53022 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d13350, d53022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d13350, d53022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro46889 (p : Pattern) (ha : d22225 p = 1) (hb : d53010 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d1527 q = 1) (hb : d52968 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1527, d52968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro199 q ha hb
    | true =>
      simp only [d1527, d52968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro200 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1528 q = 1) (hb : d52969 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1528, d52969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1528, d52969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro147 q ha hb
  have h3 (q : Pattern) (ha : d1529 q = 1) (hb : d52970 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1529, d52970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1529, d52970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d52986 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d10051 q = 1) (hb : d52987 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d10051, d52987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10051, d52987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d52992 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d10052 q = 1) (hb : d52993 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d10052, d52993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10052, d52993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d10053 q = 1) (hb : d52994 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d10053, d52994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10053, d52994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d53009 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d22225 q = 1) (hb : d53010 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d22225, d53010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d22225, d53010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro46890 (p : Pattern) (ha : d53027 p = 1) (hb : d196644 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53027 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d22226 q = 1) (hb : d53011 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22226, d53011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46889 q ha hb
    | true =>
      simp only [d22226, d53011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22227 q = 1) (hb : d53012 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22227, d53012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22227, d53012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d22228 q = 1) (hb : d53013 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d22228, d53013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d22228, d53013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22229 q = 1) (hb : d53014 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d22229, d53014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d22229, d53014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d13351 q = 1) (hb : d53023 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13351, d53023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46888 q ha hb
    | true =>
      simp only [d13351, d53023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d13352 q = 1) (hb : d53024 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13352, d53024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13352, d53024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d13353 q = 1) (hb : d53025 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13353, d53025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d13353, d53025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d13354 q = 1) (hb : d53026 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13354, d53026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d13354, d53026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d22230 q = 1) (hb : d53027 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22230, d53027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22230, d53027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d53027 q = 1) (hb : d196644 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d196644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d196644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro46891 (p : Pattern) (ha : d13350 p = 1) (hb : d69220 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d1543 q = 1) (hb : d52984 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1543, d52984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro202 q ha hb
    | true =>
      simp only [d1543, d52984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro203 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1544 q = 1) (hb : d52985 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1544, d52985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1544, d52985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro148 q ha hb
  have h3 (q : Pattern) (ha : d1545 q = 1) (hb : d52986 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1545, d52986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1545, d52986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d53004 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d10057 q = 1) (hb : d69210 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d10057, d69210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7963 q ha hb
    | true =>
      simp only [d10057, d69210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10058 q = 1) (hb : d69211 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d10058, d69211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10058, d69211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d10080 q = 1) (hb : d69212 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d10080, d69212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10080, d69212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1549 q = 1) (hb : d52990 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1549, d52990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro204 q ha hb
    | true =>
      simp only [d1549, d52990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h9 (q : Pattern) (ha : d1550 q = 1) (hb : d52991 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1550, d52991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1550, d52991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d53006 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d10081 q = 1) (hb : d53007 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d10081, d53007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d10081, d53007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d10082 q = 1) (hb : d69213 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d10082, d69213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10082, d69213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d10083 q = 1) (hb : d69214 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d10083, d69214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d10083, d69214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d69219 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d13350 q = 1) (hb : d69220 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d13350, d69220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d13350, d69220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro46892 (p : Pattern) (ha : d69225 p = 1) (hb : d196645 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d69225 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d13351 q = 1) (hb : d69221 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13351, d69221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46891 q ha hb
    | true =>
      simp only [d13351, d69221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13352 q = 1) (hb : d69222 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13352, d69222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13352, d69222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d13353 q = 1) (hb : d69223 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13353, d69223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d13353, d69223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13354 q = 1) (hb : d69224 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13354, d69224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13354, d69224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d22238 q = 1) (hb : d69225 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22238, d69225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22238, d69225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d69225 q = 1) (hb : d196645 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d196645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d196645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  exact h7 p ha hb
theorem andIntro46893 (p : Pattern) (ha : d195761 p = 1) (hb : d196656 p = 1) : d197526 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d195757 q = 1) (hb : d196646 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d195757, d196646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46890 q ha hb
    | true =>
      simp only [d195757, d196646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46892 q ha hb
  have h2 (q : Pattern) (ha : d195758 q = 1) (hb : d196647 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d195758, d196647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195758, d196647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d195759 q = 1) (hb : d196648 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d195759, d196648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195759, d196648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d195759 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d195759 q = 1) (hb : d196649 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d196649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d196649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d1 q = 1) (hb : d196654 q = 1) : d196654 q = 1 := by
    exact hb
  have h7 (q : Pattern) (ha : d195760 q = 1) (hb : d196655 q = 1) : d197525 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d195760, d196655, d197525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d195760, d196655, d197525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d195761 q = 1) (hb : d196656 q = 1) : d197526 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d195761, d196656, d197526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d195761, d196656, d197526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro46894 (p : Pattern) (ha : d195767 p = 1) (hb : d196666 p = 1) : d197532 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d195762 q = 1) (hb : d196657 q = 1) : d197527 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d195762, d196657, d197527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46893 q ha hb
    | true =>
      simp only [d195762, d196657, d197527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d195763 q = 1) (hb : d196658 q = 1) : d197528 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d195763, d196658, d197528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195763, d196658, d197528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1 q = 1) (hb : d196662 q = 1) : d196662 q = 1 := by
    exact hb
  have h4 (q : Pattern) (ha : d195764 q = 1) (hb : d196663 q = 1) : d197529 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d195764, d196663, d197529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d195764, d196663, d197529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d195765 q = 1) (hb : d196664 q = 1) : d197530 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d195765, d196664, d197530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d195765, d196664, d197530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d195766 q = 1) (hb : d196665 q = 1) : d197531 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d195766, d196665, d197531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d195766, d196665, d197531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d195767 q = 1) (hb : d196666 q = 1) : d197532 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d195767, d196666, d197532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195767, d196666, d197532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro46895 (p : Pattern) (ha : d195773 p = 1) (hb : d196676 p = 1) : d197538 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d196670 q = 1) : d196670 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d195768 q = 1) (hb : d196671 q = 1) : d197533 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195768, d196671, d197533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46894 q ha hb
    | true =>
      simp only [d195768, d196671, d197533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d195769 q = 1) (hb : d196672 q = 1) : d197534 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d195769, d196672, d197534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195769, d196672, d197534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d195770 q = 1) (hb : d196673 q = 1) : d197535 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d195770, d196673, d197535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d195770, d196673, d197535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d195771 q = 1) (hb : d196674 q = 1) : d197536 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d195771, d196674, d197536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195771, d196674, d197536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d195772 q = 1) (hb : d196675 q = 1) : d197537 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d195772, d196675, d197537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195772, d196675, d197537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d195773 q = 1) (hb : d196676 q = 1) : d197538 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d195773, d196676, d197538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195773, d196676, d197538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro46896 (p : Pattern) (ha : d195776 p = 1) (hb : d196679 p = 1) : d197541 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d195762 q = 1) (hb : d196657 q = 1) : d197527 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d195762, d196657, d197527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46893 q ha hb
    | true =>
      simp only [d195762, d196657, d197527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d195763 q = 1) (hb : d196658 q = 1) : d197528 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d195763, d196658, d197528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195763, d196658, d197528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1 q = 1) (hb : d196662 q = 1) : d196662 q = 1 := by
    exact hb
  have h4 (q : Pattern) (ha : d195764 q = 1) (hb : d196663 q = 1) : d197529 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d195764, d196663, d197529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d195764, d196663, d197529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d195765 q = 1) (hb : d196664 q = 1) : d197530 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d195765, d196664, d197530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d195765, d196664, d197530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d195766 q = 1) (hb : d196665 q = 1) : d197531 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d195766, d196665, d197531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d195766, d196665, d197531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d195776 q = 1) (hb : d196679 q = 1) : d197541 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d195776, d196679, d197541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d195776, d196679, d197541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro46897 (p : Pattern) (ha : d195782 p = 1) (hb : d196686 p = 1) : d197547 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d196670 q = 1) : d196670 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d195768 q = 1) (hb : d196671 q = 1) : d197533 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195768, d196671, d197533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46894 q ha hb
    | true =>
      simp only [d195768, d196671, d197533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d195769 q = 1) (hb : d196672 q = 1) : d197534 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d195769, d196672, d197534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195769, d196672, d197534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d195770 q = 1) (hb : d196673 q = 1) : d197535 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d195770, d196673, d197535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d195770, d196673, d197535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d195771 q = 1) (hb : d196674 q = 1) : d197536 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d195771, d196674, d197536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195771, d196674, d197536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d195772 q = 1) (hb : d196675 q = 1) : d197537 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d195772, d196675, d197537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195772, d196675, d197537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1 q = 1) (hb : d196680 q = 1) : d196680 q = 1 := by
    exact hb
  have h8 (q : Pattern) (ha : d195777 q = 1) (hb : d196681 q = 1) : d197542 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195777, d196681, d197542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46896 q ha hb
    | true =>
      simp only [d195777, d196681, d197542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d195778 q = 1) (hb : d196682 q = 1) : d197543 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d195778, d196682, d197543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195778, d196682, d197543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d195779 q = 1) (hb : d196683 q = 1) : d197544 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d195779, d196683, d197544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d195779, d196683, d197544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d195780 q = 1) (hb : d196684 q = 1) : d197545 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d195780, d196684, d197545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195780, d196684, d197545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d195781 q = 1) (hb : d196685 q = 1) : d197546 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d195781, d196685, d197546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195781, d196685, d197546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d195782 q = 1) (hb : d196686 q = 1) : d197547 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d195782, d196686, d197547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d195782, d196686, d197547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro46898 (p : Pattern) (ha : d195761 p = 1) (hb : d196727 p = 1) : d197570 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d195757 q = 1) (hb : d196646 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d195757, d196646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46890 q ha hb
    | true =>
      simp only [d195757, d196646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46892 q ha hb
  have h2 (q : Pattern) (ha : d195758 q = 1) (hb : d196647 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d195758, d196647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195758, d196647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d195759 q = 1) (hb : d196648 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d195759, d196648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195759, d196648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d195759 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d195759 q = 1) (hb : d196649 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d196649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d196649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d1 q = 1) (hb : d196725 q = 1) : d196725 q = 1 := by
    exact hb
  have h7 (q : Pattern) (ha : d195760 q = 1) (hb : d196726 q = 1) : d197569 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d195760, d196726, d197569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d195760, d196726, d197569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d195761 q = 1) (hb : d196727 q = 1) : d197570 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d195761, d196727, d197570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d195761, d196727, d197570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro46899 (p : Pattern) (ha : d195767 p = 1) (hb : d196733 p = 1) : d197576 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d195762 q = 1) (hb : d196728 q = 1) : d197571 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d195762, d196728, d197571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46898 q ha hb
    | true =>
      simp only [d195762, d196728, d197571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d195763 q = 1) (hb : d196729 q = 1) : d197572 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d195763, d196729, d197572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195763, d196729, d197572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d195764 q = 1) (hb : d196730 q = 1) : d197573 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d195764, d196730, d197573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d195764, d196730, d197573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d195765 q = 1) (hb : d196731 q = 1) : d197574 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d195765, d196731, d197574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d195765, d196731, d197574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d195766 q = 1) (hb : d196732 q = 1) : d197575 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d195766, d196732, d197575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d195766, d196732, d197575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d195767 q = 1) (hb : d196733 q = 1) : d197576 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d195767, d196733, d197576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195767, d196733, d197576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro46900 (p : Pattern) (ha : d195787 p = 1) (hb : d196691 p = 1) : d197552 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d195762 q = 1) (hb : d196657 q = 1) : d197527 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d195762, d196657, d197527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46893 q ha hb
    | true =>
      simp only [d195762, d196657, d197527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d195763 q = 1) (hb : d196658 q = 1) : d197528 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d195763, d196658, d197528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195763, d196658, d197528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1 q = 1) (hb : d196662 q = 1) : d196662 q = 1 := by
    exact hb
  have h4 (q : Pattern) (ha : d195764 q = 1) (hb : d196663 q = 1) : d197529 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d195764, d196663, d197529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d195764, d196663, d197529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d195765 q = 1) (hb : d196664 q = 1) : d197530 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d195765, d196664, d197530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d195765, d196664, d197530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d195786 q = 1) (hb : d196690 q = 1) : d197551 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d195786, d196690, d197551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195786, d196690, d197551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d195787 q = 1) (hb : d196691 q = 1) : d197552 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d195787, d196691, d197552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195787, d196691, d197552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro46901 (p : Pattern) (ha : d195794 p = 1) (hb : d196700 p = 1) : d197559 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d195762 q = 1) (hb : d196657 q = 1) : d197527 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d195762, d196657, d197527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46893 q ha hb
    | true =>
      simp only [d195762, d196657, d197527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d195763 q = 1) (hb : d196658 q = 1) : d197528 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d195763, d196658, d197528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195763, d196658, d197528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1 q = 1) (hb : d196662 q = 1) : d196662 q = 1 := by
    exact hb
  have h4 (q : Pattern) (ha : d195764 q = 1) (hb : d196663 q = 1) : d197529 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d195764, d196663, d197529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d195764, d196663, d197529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d195792 q = 1) (hb : d196698 q = 1) : d197557 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d195792, d196698, d197557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195792, d196698, d197557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d195793 q = 1) (hb : d196699 q = 1) : d197558 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d195793, d196699, d197558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d195793, d196699, d197558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d195794 q = 1) (hb : d196700 q = 1) : d197559 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d195794, d196700, d197559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195794, d196700, d197559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro46902 (p : Pattern) (ha : d53015 p = 1) (hb : d196707 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53015 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10046 q = 1) (hb : d52996 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10046, d52996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35636 q ha hb
    | true =>
      simp only [d10046, d52996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10048 q = 1) (hb : d52997 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10048, d52997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10048, d52997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d15229 q = 1) (hb : d52998 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15229, d52998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d15229, d52998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15230 q = 1) (hb : d52999 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15230, d52999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15230, d52999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d22226 q = 1) (hb : d53011 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22226, d53011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46889 q ha hb
    | true =>
      simp only [d22226, d53011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d22227 q = 1) (hb : d53012 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22227, d53012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22227, d53012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d22228 q = 1) (hb : d53013 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d22228, d53013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d22228, d53013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d22229 q = 1) (hb : d53014 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d22229, d53014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d22229, d53014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d22318 q = 1) (hb : d53015 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22318, d53015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22318, d53015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d53015 q = 1) (hb : d196707 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d196707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d196707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro46903 (p : Pattern) (ha : d22225 p = 1) (hb : d101525 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d1527 q = 1) (hb : d52968 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1527, d52968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro199 q ha hb
    | true =>
      simp only [d1527, d52968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro200 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1528 q = 1) (hb : d52969 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1528, d52969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1528, d52969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro147 q ha hb
  have h3 (q : Pattern) (ha : d1529 q = 1) (hb : d52970 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1529, d52970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1529, d52970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d101483 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d10051 q = 1) (hb : d101522 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d10051, d101522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10051, d101522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10052 q = 1) (hb : d101523 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d10052, d101523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10052, d101523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d10053 q = 1) (hb : d101524 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d10053, d101524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10053, d101524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d101488 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d22225 q = 1) (hb : d101525 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d22225, d101525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22225, d101525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro46904 (p : Pattern) (ha : d113615 p = 1) (hb : d196644 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d113615 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d22226 q = 1) (hb : d101526 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22226, d101526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46903 q ha hb
    | true =>
      simp only [d22226, d101526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22227 q = 1) (hb : d101528 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22227, d101528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22227, d101528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d22228 q = 1) (hb : d113608 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d22228, d113608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d22228, d113608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22229 q = 1) (hb : d113609 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d22229, d113609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d22229, d113609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d13351 q = 1) (hb : d113611 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13351, d113611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29819 q ha hb
    | true =>
      simp only [d13351, d113611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d13352 q = 1) (hb : d113612 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13352, d113612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13352, d113612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d13353 q = 1) (hb : d113613 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13353, d113613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d13353, d113613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d13354 q = 1) (hb : d113614 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13354, d113614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d13354, d113614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d22230 q = 1) (hb : d113615 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22230, d113615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22230, d113615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d113615 q = 1) (hb : d196644 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d196644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d196644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro46905 (p : Pattern) (ha : d195802 p = 1) (hb : d196713 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d195798 q = 1) (hb : d196708 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d195798, d196708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46902 q ha hb
    | true =>
      simp only [d195798, d196708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46904 q ha hb
  have h2 (q : Pattern) (ha : d195799 q = 1) (hb : d196709 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d195799, d196709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195799, d196709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d195800 q = 1) (hb : d196710 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d195800, d196710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195800, d196710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d195800 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d195800 q = 1) (hb : d196711 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d196711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d196711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d195757 q = 1) (hb : d196646 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d195757, d196646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46890 q ha hb
    | true =>
      simp only [d195757, d196646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46892 q ha hb
  have h7 (q : Pattern) (ha : d195758 q = 1) (hb : d196647 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d195758, d196647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195758, d196647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d195759 q = 1) (hb : d196648 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d195759, d196648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195759, d196648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d195759 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d195759 q = 1) (hb : d196649 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d196649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d196649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d195801 q = 1) (hb : d196712 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d195801, d196712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d195801, d196712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d195802 q = 1) (hb : d196713 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d195802, d196713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d195802, d196713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h12 p ha hb
theorem andIntro46906 (p : Pattern) (ha : d195808 p = 1) (hb : d196719 p = 1) : d197566 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d195803 q = 1) (hb : d196714 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d195803, d196714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46905 q ha hb
    | true =>
      simp only [d195803, d196714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d195804 q = 1) (hb : d196715 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d195804, d196715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195804, d196715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d195762 q = 1) (hb : d196657 q = 1) : d197527 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d195762, d196657, d197527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46893 q ha hb
    | true =>
      simp only [d195762, d196657, d197527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d195763 q = 1) (hb : d196658 q = 1) : d197528 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d195763, d196658, d197528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195763, d196658, d197528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d195805 q = 1) (hb : d196716 q = 1) : d197563 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d195805, d196716, d197563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d195805, d196716, d197563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d195806 q = 1) (hb : d196717 q = 1) : d197564 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d195806, d196717, d197564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d195806, d196717, d197564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d195807 q = 1) (hb : d196718 q = 1) : d197565 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d195807, d196718, d197565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d195807, d196718, d197565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d195808 q = 1) (hb : d196719 q = 1) : d197566 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d195808, d196719, d197566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195808, d196719, d197566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro46907 (p : Pattern) (ha : d195815 p = 1) (hb : d196739 p = 1) : d197582 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d196693 q = 1) : d196693 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d195788 q = 1) (hb : d196694 q = 1) : d197553 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195788, d196694, d197553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46900 q ha hb
    | true =>
      simp only [d195788, d196694, d197553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d195789 q = 1) (hb : d196695 q = 1) : d197554 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d195789, d196695, d197554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195789, d196695, d197554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d195790 q = 1) (hb : d196696 q = 1) : d197555 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d195790, d196696, d197555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d195790, d196696, d197555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d195791 q = 1) (hb : d196697 q = 1) : d197556 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d195791, d196697, d197556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195791, d196697, d197556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1 q = 1) (hb : d196703 q = 1) : d196703 q = 1 := by
    exact hb
  have h7 (q : Pattern) (ha : d195795 q = 1) (hb : d196704 q = 1) : d197560 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195795, d196704, d197560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46901 q ha hb
    | true =>
      simp only [d195795, d196704, d197560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d195796 q = 1) (hb : d196705 q = 1) : d197561 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d195796, d196705, d197561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195796, d196705, d197561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d195797 q = 1) (hb : d196706 q = 1) : d197562 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d195797, d196706, d197562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d195797, d196706, d197562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d195809 q = 1) (hb : d196720 q = 1) : d197567 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195809, d196720, d197567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46906 q ha hb
    | true =>
      simp only [d195809, d196720, d197567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46894 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d195768 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d195810 q = 1) (hb : d196721 q = 1) : d197568 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d195810, d196721, d197568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d195810, d196721, d197568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d195768 q = 1) (hb : d196734 q = 1) : d197577 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195768, d196734, d197577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46899 q ha hb
    | true =>
      simp only [d195768, d196734, d197577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d195811 q = 1) (hb : d196735 q = 1) : d197578 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d195811, d196735, d197578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d195811, d196735, d197578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d195812 q = 1) (hb : d196736 q = 1) : d197579 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d195812, d196736, d197579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d195812, d196736, d197579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d195813 q = 1) (hb : d196737 q = 1) : d197580 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d195813, d196737, d197580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d195813, d196737, d197580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d195814 q = 1) (hb : d196738 q = 1) : d197581 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d195814, d196738, d197581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d195814, d196738, d197581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d195815 q = 1) (hb : d196739 q = 1) : d197582 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d195815, d196739, d197582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195815, d196739, d197582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro46908 (p : Pattern) (ha : d195776 p = 1) (hb : d196754 p = 1) : d197595 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d195762 q = 1) (hb : d196728 q = 1) : d197571 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d195762, d196728, d197571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46898 q ha hb
    | true =>
      simp only [d195762, d196728, d197571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d195763 q = 1) (hb : d196729 q = 1) : d197572 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d195763, d196729, d197572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195763, d196729, d197572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d195764 q = 1) (hb : d196730 q = 1) : d197573 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d195764, d196730, d197573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d195764, d196730, d197573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d195765 q = 1) (hb : d196731 q = 1) : d197574 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d195765, d196731, d197574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d195765, d196731, d197574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d195766 q = 1) (hb : d196732 q = 1) : d197575 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d195766, d196732, d197575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d195766, d196732, d197575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d195776 q = 1) (hb : d196754 q = 1) : d197595 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d195776, d196754, d197595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d195776, d196754, d197595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro46909 (p : Pattern) (ha : d195816 p = 1) (hb : d196740 p = 1) : d197583 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d195762 q = 1) (hb : d196657 q = 1) : d197527 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d195762, d196657, d197527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46893 q ha hb
    | true =>
      simp only [d195762, d196657, d197527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d195763 q = 1) (hb : d196658 q = 1) : d197528 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d195763, d196658, d197528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195763, d196658, d197528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1 q = 1) (hb : d196662 q = 1) : d196662 q = 1 := by
    exact hb
  have h4 (q : Pattern) (ha : d195764 q = 1) (hb : d196663 q = 1) : d197529 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d195764, d196663, d197529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d195764, d196663, d197529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d195765 q = 1) (hb : d196664 q = 1) : d197530 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d195765, d196664, d197530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d195765, d196664, d197530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d195786 q = 1) (hb : d196690 q = 1) : d197551 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d195786, d196690, d197551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195786, d196690, d197551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d195816 q = 1) (hb : d196740 q = 1) : d197583 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d195816, d196740, d197583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d195816, d196740, d197583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro46910 (p : Pattern) (ha : d195821 p = 1) (hb : d196746 p = 1) : d197588 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d195762 q = 1) (hb : d196657 q = 1) : d197527 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d195762, d196657, d197527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46893 q ha hb
    | true =>
      simp only [d195762, d196657, d197527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d195763 q = 1) (hb : d196658 q = 1) : d197528 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d195763, d196658, d197528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195763, d196658, d197528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1 q = 1) (hb : d196662 q = 1) : d196662 q = 1 := by
    exact hb
  have h4 (q : Pattern) (ha : d195764 q = 1) (hb : d196663 q = 1) : d197529 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d195764, d196663, d197529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d195764, d196663, d197529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d195792 q = 1) (hb : d196698 q = 1) : d197557 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d195792, d196698, d197557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195792, d196698, d197557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d195793 q = 1) (hb : d196699 q = 1) : d197558 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d195793, d196699, d197558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d195793, d196699, d197558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d195821 q = 1) (hb : d196746 q = 1) : d197588 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d195821, d196746, d197588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d195821, d196746, d197588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro46911 (p : Pattern) (ha : d195825 p = 1) (hb : d196751 p = 1) : d197592 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d195803 q = 1) (hb : d196714 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d195803, d196714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46905 q ha hb
    | true =>
      simp only [d195803, d196714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d195804 q = 1) (hb : d196715 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d195804, d196715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195804, d196715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d195762 q = 1) (hb : d196657 q = 1) : d197527 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d195762, d196657, d197527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46893 q ha hb
    | true =>
      simp only [d195762, d196657, d197527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d195763 q = 1) (hb : d196658 q = 1) : d197528 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d195763, d196658, d197528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195763, d196658, d197528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d195805 q = 1) (hb : d196716 q = 1) : d197563 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d195805, d196716, d197563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d195805, d196716, d197563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d195806 q = 1) (hb : d196717 q = 1) : d197564 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d195806, d196717, d197564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d195806, d196717, d197564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d195807 q = 1) (hb : d196718 q = 1) : d197565 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d195807, d196718, d197565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d195807, d196718, d197565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d195825 q = 1) (hb : d196751 q = 1) : d197592 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d195825, d196751, d197592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d195825, d196751, d197592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro46912 (p : Pattern) (ha : d195832 p = 1) (hb : d196760 p = 1) : d197601 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d196693 q = 1) : d196693 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d195788 q = 1) (hb : d196694 q = 1) : d197553 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195788, d196694, d197553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46900 q ha hb
    | true =>
      simp only [d195788, d196694, d197553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d195789 q = 1) (hb : d196695 q = 1) : d197554 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d195789, d196695, d197554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195789, d196695, d197554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d195790 q = 1) (hb : d196696 q = 1) : d197555 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d195790, d196696, d197555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d195790, d196696, d197555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d195791 q = 1) (hb : d196697 q = 1) : d197556 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d195791, d196697, d197556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195791, d196697, d197556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1 q = 1) (hb : d196703 q = 1) : d196703 q = 1 := by
    exact hb
  have h7 (q : Pattern) (ha : d195795 q = 1) (hb : d196704 q = 1) : d197560 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195795, d196704, d197560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46901 q ha hb
    | true =>
      simp only [d195795, d196704, d197560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d195796 q = 1) (hb : d196705 q = 1) : d197561 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d195796, d196705, d197561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195796, d196705, d197561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d195797 q = 1) (hb : d196706 q = 1) : d197562 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d195797, d196706, d197562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d195797, d196706, d197562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d195809 q = 1) (hb : d196720 q = 1) : d197567 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195809, d196720, d197567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46906 q ha hb
    | true =>
      simp only [d195809, d196720, d197567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46894 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d195768 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d195810 q = 1) (hb : d196721 q = 1) : d197568 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d195810, d196721, d197568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d195810, d196721, d197568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d195768 q = 1) (hb : d196734 q = 1) : d197577 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195768, d196734, d197577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46899 q ha hb
    | true =>
      simp only [d195768, d196734, d197577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d195811 q = 1) (hb : d196735 q = 1) : d197578 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d195811, d196735, d197578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d195811, d196735, d197578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d195812 q = 1) (hb : d196736 q = 1) : d197579 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d195812, d196736, d197579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d195812, d196736, d197579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d195813 q = 1) (hb : d196737 q = 1) : d197580 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d195813, d196737, d197580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d195813, d196737, d197580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d195814 q = 1) (hb : d196738 q = 1) : d197581 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d195814, d196738, d197581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d195814, d196738, d197581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d1 q = 1) (hb : d196741 q = 1) : d196741 q = 1 := by
    exact hb
  have h19 (q : Pattern) (ha : d195817 q = 1) (hb : d196742 q = 1) : d197584 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195817, d196742, d197584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46909 q ha hb
    | true =>
      simp only [d195817, d196742, d197584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d195818 q = 1) (hb : d196743 q = 1) : d197585 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d195818, d196743, d197585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195818, d196743, d197585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d195819 q = 1) (hb : d196744 q = 1) : d197586 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d195819, d196744, d197586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d195819, d196744, d197586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d195820 q = 1) (hb : d196745 q = 1) : d197587 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d195820, d196745, d197587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195820, d196745, d197587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d1 q = 1) (hb : d196747 q = 1) : d196747 q = 1 := by
    exact hb
  have h24 (q : Pattern) (ha : d195822 q = 1) (hb : d196748 q = 1) : d197589 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195822, d196748, d197589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46910 q ha hb
    | true =>
      simp only [d195822, d196748, d197589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d195823 q = 1) (hb : d196749 q = 1) : d197590 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d195823, d196749, d197590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195823, d196749, d197590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
  have h26 (q : Pattern) (ha : d195824 q = 1) (hb : d196750 q = 1) : d197591 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d195824, d196750, d197591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d195824, d196750, d197591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d195826 q = 1) (hb : d196752 q = 1) : d197593 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195826, d196752, d197593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46911 q ha hb
    | true =>
      simp only [d195826, d196752, d197593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46896 q ha hb
  have h28 (q : Pattern) (ha : d0 q = 1) (hb : d195777 q = 1) : d0 q = 1 := by
    exact ha
  have h29 (q : Pattern) (ha : d195827 q = 1) (hb : d196753 q = 1) : d197594 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d195827, d196753, d197594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
    | true =>
      simp only [d195827, d196753, d197594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q hb ha
  have h30 (q : Pattern) (ha : d195777 q = 1) (hb : d196755 q = 1) : d197596 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195777, d196755, d197596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46908 q ha hb
    | true =>
      simp only [d195777, d196755, d197596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h31 (q : Pattern) (ha : d195828 q = 1) (hb : d196756 q = 1) : d197597 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d195828, d196756, d197597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
    | true =>
      simp only [d195828, d196756, d197597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h32 (q : Pattern) (ha : d195829 q = 1) (hb : d196757 q = 1) : d197598 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d195829, d196757, d197598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
    | true =>
      simp only [d195829, d196757, d197598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
  have h33 (q : Pattern) (ha : d195830 q = 1) (hb : d196758 q = 1) : d197599 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d195830, d196758, d197599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d195830, d196758, d197599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h32 q ha hb
  have h34 (q : Pattern) (ha : d195831 q = 1) (hb : d196759 q = 1) : d197600 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d195831, d196759, d197600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d195831, d196759, d197600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h33 q ha hb
  have h35 (q : Pattern) (ha : d195832 q = 1) (hb : d196760 q = 1) : d197601 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d195832, d196760, d197601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d195832, d196760, d197601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h34 q ha hb
  exact h35 p ha hb
theorem andIntro46913 (p : Pattern) (ha : d195834 p = 1) (hb : d196767 p = 1) : d197603 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d196670 q = 1) : d196670 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d195768 q = 1) (hb : d196671 q = 1) : d197533 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195768, d196671, d197533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46894 q ha hb
    | true =>
      simp only [d195768, d196671, d197533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d195769 q = 1) (hb : d196672 q = 1) : d197534 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d195769, d196672, d197534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195769, d196672, d197534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d195770 q = 1) (hb : d196673 q = 1) : d197535 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d195770, d196673, d197535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d195770, d196673, d197535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d195771 q = 1) (hb : d196674 q = 1) : d197536 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d195771, d196674, d197536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195771, d196674, d197536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d195772 q = 1) (hb : d196675 q = 1) : d197537 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d195772, d196675, d197537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195772, d196675, d197537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1 q = 1) (hb : d196766 q = 1) : d196766 q = 1 := by
    exact hb
  have h8 (q : Pattern) (ha : d195834 q = 1) (hb : d196767 q = 1) : d197603 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d195834, d196767, d197603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d195834, d196767, d197603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro46914 (p : Pattern) (ha : d195841 p = 1) (hb : d196780 p = 1) : d197610 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d195826 q = 1) (hb : d196752 q = 1) : d197593 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195826, d196752, d197593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46911 q ha hb
    | true =>
      simp only [d195826, d196752, d197593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46896 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d195777 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d195827 q = 1) (hb : d196753 q = 1) : d197594 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d195827, d196753, d197594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d195827, d196753, d197594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d195777 q = 1) (hb : d196755 q = 1) : d197596 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195777, d196755, d197596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46908 q ha hb
    | true =>
      simp only [d195777, d196755, d197596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d195828 q = 1) (hb : d196756 q = 1) : d197597 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d195828, d196756, d197597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d195828, d196756, d197597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d195829 q = 1) (hb : d196757 q = 1) : d197598 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d195829, d196757, d197598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d195829, d196757, d197598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d195839 q = 1) (hb : d196778 q = 1) : d197608 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d195839, d196778, d197608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195839, d196778, d197608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d195840 q = 1) (hb : d196779 q = 1) : d197609 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d195840, d196779, d197609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195840, d196779, d197609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d195841 q = 1) (hb : d196780 q = 1) : d197610 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d195841, d196780, d197610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195841, d196780, d197610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro46915 (p : Pattern) (ha : d53192 p = 1) (hb : d196788 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53192 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d15380 q = 1) (hb : d53183 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15380, d53183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d15380, d53183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35636 q ha hb
  have h3 (q : Pattern) (ha : d10046 q = 1) (hb : d52996 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10046, d52996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35636 q ha hb
    | true =>
      simp only [d10046, d52996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d15381 q = 1) (hb : d53184 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15381, d53184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15381, d53184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10048 q = 1) (hb : d52997 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10048, d52997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10048, d52997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d15382 q = 1) (hb : d53185 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15382, d53185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15382, d53185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d15383 q = 1) (hb : d53186 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15383, d53186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15383, d53186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d22502 q = 1) (hb : d53188 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22502, d53188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d22502, d53188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46889 q ha hb
  have h9 (q : Pattern) (ha : d22226 q = 1) (hb : d53011 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22226, d53011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46889 q ha hb
    | true =>
      simp only [d22226, d53011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d22503 q = 1) (hb : d53189 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22503, d53189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d22503, d53189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d22227 q = 1) (hb : d53012 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22227, d53012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d22227, d53012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h12 (q : Pattern) (ha : d22504 q = 1) (hb : d53190 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d22504, d53190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d22504, d53190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d22505 q = 1) (hb : d53191 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d22505, d53191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d22505, d53191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h14 (q : Pattern) (ha : d22506 q = 1) (hb : d53192 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22506, d53192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22506, d53192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d53192 q = 1) (hb : d196788 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d196788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d196788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  exact h15 p ha hb
theorem andIntro46916 (p : Pattern) (ha : d53198 p = 1) (hb : d196789 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53198 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d22502 q = 1) (hb : d53188 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22502, d53188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d22502, d53188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46889 q ha hb
  have h3 (q : Pattern) (ha : d22226 q = 1) (hb : d53011 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22226, d53011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46889 q ha hb
    | true =>
      simp only [d22226, d53011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d22503 q = 1) (hb : d53189 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22503, d53189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22503, d53189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22227 q = 1) (hb : d53012 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22227, d53012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22227, d53012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d22504 q = 1) (hb : d53190 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d22504, d53190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d22504, d53190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d22505 q = 1) (hb : d53191 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d22505, d53191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22505, d53191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d13490 q = 1) (hb : d53194 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13490, d53194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d13490, d53194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46888 q ha hb
  have h9 (q : Pattern) (ha : d13351 q = 1) (hb : d53023 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13351, d53023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46888 q ha hb
    | true =>
      simp only [d13351, d53023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d13491 q = 1) (hb : d53195 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13491, d53195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d13491, d53195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d13352 q = 1) (hb : d53024 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13352, d53024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d13352, d53024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h12 (q : Pattern) (ha : d13492 q = 1) (hb : d53196 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13492, d53196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d13492, d53196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d13493 q = 1) (hb : d53197 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13493, d53197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d13493, d53197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h14 (q : Pattern) (ha : d22513 q = 1) (hb : d53198 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22513, d53198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22513, d53198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d53198 q = 1) (hb : d196789 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d196789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d196789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  exact h15 p ha hb
theorem andIntro46917 (p : Pattern) (ha : d76229 p = 1) (hb : d196794 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d76229 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d13490 q = 1) (hb : d76225 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13490, d76225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d13490, d76225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46891 q ha hb
  have h3 (q : Pattern) (ha : d13351 q = 1) (hb : d69221 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13351, d69221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46891 q ha hb
    | true =>
      simp only [d13351, d69221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d13491 q = 1) (hb : d76226 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13491, d76226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13491, d76226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13352 q = 1) (hb : d69222 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13352, d69222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13352, d69222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d13492 q = 1) (hb : d76227 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13492, d76227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13492, d76227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d13493 q = 1) (hb : d76228 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13493, d76228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13493, d76228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d22523 q = 1) (hb : d76229 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22523, d76229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22523, d76229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h9 (q : Pattern) (ha : d76229 q = 1) (hb : d196794 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d196794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d196794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  exact h9 p ha hb
theorem andIntro46918 (p : Pattern) (ha : d113716 p = 1) (hb : d196789 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d113716 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d22502 q = 1) (hb : d113708 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22502, d113708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d22502, d113708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46903 q ha hb
  have h3 (q : Pattern) (ha : d22226 q = 1) (hb : d101526 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22226, d101526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46903 q ha hb
    | true =>
      simp only [d22226, d101526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d22503 q = 1) (hb : d113709 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22503, d113709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22503, d113709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22227 q = 1) (hb : d101528 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22227, d101528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22227, d101528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d22504 q = 1) (hb : d113710 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d22504, d113710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d22504, d113710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d22505 q = 1) (hb : d113711 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d22505, d113711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22505, d113711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d13490 q = 1) (hb : d113712 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13490, d113712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d13490, d113712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29819 q ha hb
  have h9 (q : Pattern) (ha : d13351 q = 1) (hb : d113611 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13351, d113611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29819 q ha hb
    | true =>
      simp only [d13351, d113611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d13491 q = 1) (hb : d113713 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13491, d113713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d13491, d113713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d13352 q = 1) (hb : d113612 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13352, d113612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d13352, d113612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h12 (q : Pattern) (ha : d13492 q = 1) (hb : d113714 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13492, d113714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d13492, d113714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d13493 q = 1) (hb : d113715 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13493, d113715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d13493, d113715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h14 (q : Pattern) (ha : d22513 q = 1) (hb : d113716 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22513, d113716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22513, d113716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d113716 q = 1) (hb : d196789 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d196789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d196789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  exact h15 p ha hb
theorem andIntro46919 (p : Pattern) (ha : d195854 p = 1) (hb : d196800 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d195847 q = 1) (hb : d196790 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d195847, d196790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46915 q ha hb
    | true =>
      simp only [d195847, d196790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46918 q ha hb
  have h2 (q : Pattern) (ha : d195848 q = 1) (hb : d196791 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d195848, d196791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195848, d196791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d195849 q = 1) (hb : d196792 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d195849, d196792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195849, d196792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d195849 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d195849 q = 1) (hb : d196793 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d196793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d196793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d195850 q = 1) (hb : d196795 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d195850, d196795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46916 q ha hb
    | true =>
      simp only [d195850, d196795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46917 q ha hb
  have h7 (q : Pattern) (ha : d195851 q = 1) (hb : d196796 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d195851, d196796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195851, d196796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d195852 q = 1) (hb : d196797 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d195852, d196797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195852, d196797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d195852 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d195852 q = 1) (hb : d196798 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d196798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d196798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d195853 q = 1) (hb : d196799 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d195853, d196799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d195853, d196799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d195854 q = 1) (hb : d196800 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d195854, d196800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d195854, d196800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h12 p ha hb
theorem andIntro46920 (p : Pattern) (ha : d195858 p = 1) (hb : d196809 p = 1) : d197617 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d195850 q = 1) (hb : d196795 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d195850, d196795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46916 q ha hb
    | true =>
      simp only [d195850, d196795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46917 q ha hb
  have h2 (q : Pattern) (ha : d195851 q = 1) (hb : d196796 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d195851, d196796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195851, d196796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d195852 q = 1) (hb : d196797 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d195852, d196797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195852, d196797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d195852 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d195852 q = 1) (hb : d196798 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d196798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d196798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d1 q = 1) (hb : d196807 q = 1) : d196807 q = 1 := by
    exact hb
  have h7 (q : Pattern) (ha : d195857 q = 1) (hb : d196808 q = 1) : d197616 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d195857, d196808, d197616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d195857, d196808, d197616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d195858 q = 1) (hb : d196809 q = 1) : d197617 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d195858, d196809, d197617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d195858, d196809, d197617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro46921 (p : Pattern) (ha : d195864 p = 1) (hb : d196815 p = 1) : d197623 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d195855 q = 1) (hb : d196801 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d195855, d196801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46919 q ha hb
    | true =>
      simp only [d195855, d196801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d195856 q = 1) (hb : d196802 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d195856, d196802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195856, d196802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d195859 q = 1) (hb : d196810 q = 1) : d197618 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d195859, d196810, d197618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46920 q ha hb
    | true =>
      simp only [d195859, d196810, d197618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d195860 q = 1) (hb : d196811 q = 1) : d197619 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d195860, d196811, d197619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195860, d196811, d197619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d195861 q = 1) (hb : d196812 q = 1) : d197620 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d195861, d196812, d197620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d195861, d196812, d197620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d195862 q = 1) (hb : d196813 q = 1) : d197621 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d195862, d196813, d197621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d195862, d196813, d197621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d195863 q = 1) (hb : d196814 q = 1) : d197622 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d195863, d196814, d197622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d195863, d196814, d197622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d195864 q = 1) (hb : d196815 q = 1) : d197623 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d195864, d196815, d197623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d195864, d196815, d197623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro46922 (p : Pattern) (ha : d195868 p = 1) (hb : d196823 p = 1) : d197627 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d195859 q = 1) (hb : d196810 q = 1) : d197618 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d195859, d196810, d197618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46920 q ha hb
    | true =>
      simp only [d195859, d196810, d197618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d195860 q = 1) (hb : d196811 q = 1) : d197619 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d195860, d196811, d197619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195860, d196811, d197619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1 q = 1) (hb : d196819 q = 1) : d196819 q = 1 := by
    exact hb
  have h4 (q : Pattern) (ha : d195865 q = 1) (hb : d196820 q = 1) : d197624 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d195865, d196820, d197624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d195865, d196820, d197624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d195866 q = 1) (hb : d196821 q = 1) : d197625 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d195866, d196821, d197625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d195866, d196821, d197625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d195867 q = 1) (hb : d196822 q = 1) : d197626 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d195867, d196822, d197626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d195867, d196822, d197626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d195868 q = 1) (hb : d196823 q = 1) : d197627 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d195868, d196823, d197627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d195868, d196823, d197627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro46923 (p : Pattern) (ha : d195858 p = 1) (hb : d196831 p = 1) : d197631 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d195850 q = 1) (hb : d196795 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d195850, d196795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46916 q ha hb
    | true =>
      simp only [d195850, d196795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46917 q ha hb
  have h2 (q : Pattern) (ha : d195851 q = 1) (hb : d196796 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d195851, d196796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195851, d196796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d195852 q = 1) (hb : d196797 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d195852, d196797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195852, d196797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d195852 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d195852 q = 1) (hb : d196798 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d196798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d196798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d1 q = 1) (hb : d196829 q = 1) : d196829 q = 1 := by
    exact hb
  have h7 (q : Pattern) (ha : d195857 q = 1) (hb : d196830 q = 1) : d197630 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d195857, d196830, d197630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d195857, d196830, d197630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d195858 q = 1) (hb : d196831 q = 1) : d197631 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d195858, d196831, d197631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d195858, d196831, d197631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro46924 (p : Pattern) (ha : d195868 p = 1) (hb : d196837 p = 1) : d197637 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d195859 q = 1) (hb : d196832 q = 1) : d197632 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d195859, d196832, d197632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46923 q ha hb
    | true =>
      simp only [d195859, d196832, d197632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d195860 q = 1) (hb : d196833 q = 1) : d197633 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d195860, d196833, d197633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195860, d196833, d197633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d195865 q = 1) (hb : d196834 q = 1) : d197634 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d195865, d196834, d197634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d195865, d196834, d197634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d195866 q = 1) (hb : d196835 q = 1) : d197635 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d195866, d196835, d197635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d195866, d196835, d197635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d195867 q = 1) (hb : d196836 q = 1) : d197636 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d195867, d196836, d197636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d195867, d196836, d197636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d195868 q = 1) (hb : d196837 q = 1) : d197637 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d195868, d196837, d197637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d195868, d196837, d197637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro46925 (p : Pattern) (ha : d195876 p = 1) (hb : d196843 p = 1) : d197643 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d195869 q = 1) (hb : d196824 q = 1) : d197628 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195869, d196824, d197628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46921 q ha hb
    | true =>
      simp only [d195869, d196824, d197628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46922 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d195870 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d195871 q = 1) (hb : d196825 q = 1) : d197629 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d195871, d196825, d197629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d195871, d196825, d197629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d195870 q = 1) (hb : d196838 q = 1) : d197638 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195870, d196838, d197638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46924 q ha hb
    | true =>
      simp only [d195870, d196838, d197638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d195872 q = 1) (hb : d196839 q = 1) : d197639 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d195872, d196839, d197639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d195872, d196839, d197639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d195873 q = 1) (hb : d196840 q = 1) : d197640 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d195873, d196840, d197640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d195873, d196840, d197640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d195874 q = 1) (hb : d196841 q = 1) : d197641 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d195874, d196841, d197641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195874, d196841, d197641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d195875 q = 1) (hb : d196842 q = 1) : d197642 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d195875, d196842, d197642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195875, d196842, d197642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d195876 q = 1) (hb : d196843 q = 1) : d197643 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d195876, d196843, d197643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195876, d196843, d197643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro46926 (p : Pattern) (ha : d195882 p = 1) (hb : d196860 p = 1) : d197649 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d195774 q = 1) (hb : d196677 q = 1) : d197539 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d195774, d196677, d197539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195774, d196677, d197539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46895 q ha hb
  have h2 (q : Pattern) (ha : d195775 q = 1) (hb : d196678 q = 1) : d197540 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d195775, d196678, d197540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d195775, d196678, d197540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d195783 q = 1) (hb : d196687 q = 1) : d197548 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d195783, d196687, d197548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46895 q ha hb
    | true =>
      simp only [d195783, d196687, d197548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46897 q ha hb
  have h4 (q : Pattern) (ha : d195784 q = 1) (hb : d196688 q = 1) : d197549 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d195784, d196688, d197549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d195784, d196688, d197549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d195785 q = 1) (hb : d196689 q = 1) : d197550 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d195785, d196689, d197550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d195785, d196689, d197550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d195833 q = 1) (hb : d196761 q = 1) : d197602 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d195833, d196761, d197602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46907 q ha hb
    | true =>
      simp only [d195833, d196761, d197602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46912 q ha hb
  have h7 (q : Pattern) (ha : d1 q = 1) (hb : d196773 q = 1) : d196773 q = 1 := by
    exact hb
  have h8 (q : Pattern) (ha : d195835 q = 1) (hb : d196774 q = 1) : d197604 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d195835, d196774, d197604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46913 q ha hb
    | true =>
      simp only [d195835, d196774, d197604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d195836 q = 1) (hb : d196775 q = 1) : d197605 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d195836, d196775, d197605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d195836, d196775, d197605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d195837 q = 1) (hb : d196776 q = 1) : d197606 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d195837, d196776, d197606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d195837, d196776, d197606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d195838 q = 1) (hb : d196777 q = 1) : d197607 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d195838, d196777, d197607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d195838, d196777, d197607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d195842 q = 1) (hb : d196781 q = 1) : d197611 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d195842, d196781, d197611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195842, d196781, d197611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46914 q ha hb
  have h13 (q : Pattern) (ha : d1 q = 1) (hb : d196783 q = 1) : d196783 q = 1 := by
    exact hb
  have h14 (q : Pattern) (ha : d195843 q = 1) (hb : d196784 q = 1) : d197612 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d195843, d196784, d197612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d195843, d196784, d197612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d195844 q = 1) (hb : d196785 q = 1) : d197613 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d195844, d196785, d197613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d195844, d196785, d197613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d195845 q = 1) (hb : d196786 q = 1) : d197614 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d195845, d196786, d197614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d195845, d196786, d197614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h17 (q : Pattern) (ha : d195846 q = 1) (hb : d196787 q = 1) : d197615 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d195846, d196787, d197615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d195846, d196787, d197615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d195877 q = 1) (hb : d196844 q = 1) : d197644 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d195877, d196844, d197644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195877, d196844, d197644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46925 q ha hb
  have h19 (q : Pattern) (ha : d1 q = 1) (hb : d196855 q = 1) : d196855 q = 1 := by
    exact hb
  have h20 (q : Pattern) (ha : d195878 q = 1) (hb : d196856 q = 1) : d197645 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d195878, d196856, d197645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d195878, d196856, d197645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d195879 q = 1) (hb : d196857 q = 1) : d197646 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d195879, d196857, d197646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d195879, d196857, d197646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d195880 q = 1) (hb : d196858 q = 1) : d197647 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d195880, d196858, d197647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d195880, d196858, d197647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d195881 q = 1) (hb : d196859 q = 1) : d197648 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d195881, d196859, d197648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d195881, d196859, d197648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d195882 q = 1) (hb : d196860 q = 1) : d197649 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d195882, d196860, d197649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d195882, d196860, d197649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  exact h24 p ha hb
theorem andIntro46927 (p : Pattern) (ha : d195888 p = 1) (hb : d196866 p = 1) : d197655 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d195883 q = 1) (hb : d196861 q = 1) : d197650 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d195883, d196861, d197650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195883, d196861, d197650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46926 q ha hb
  have h2 (q : Pattern) (ha : d195884 q = 1) (hb : d196862 q = 1) : d197651 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d195884, d196862, d197651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195884, d196862, d197651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d195885 q = 1) (hb : d196863 q = 1) : d197652 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d195885, d196863, d197652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195885, d196863, d197652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d195886 q = 1) (hb : d196864 q = 1) : d197653 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d195886, d196864, d197653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195886, d196864, d197653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d195887 q = 1) (hb : d196865 q = 1) : d197654 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d195887, d196865, d197654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195887, d196865, d197654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d195888 q = 1) (hb : d196866 q = 1) : d197655 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d195888, d196866, d197655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195888, d196866, d197655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro46928 (p : Pattern) (ha : d13677 p = 1) (hb : d53343 p = 1) : d0 p = 1 := by
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
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d53323 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d5715 q = 1) (hb : d53324 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d5715, d53324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5715, d53324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d53328 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d5716 q = 1) (hb : d53329 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d5716, d53329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5716, d53329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d5717 q = 1) (hb : d53330 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d5717, d53330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d5717, d53330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d53342 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d13677 q = 1) (hb : d53343 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d13677, d53343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d13677, d53343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro46929 (p : Pattern) (ha : d53348 p = 1) (hb : d196871 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53348 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10353 q = 1) (hb : d53332 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10353, d53332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35680 q ha hb
    | true =>
      simp only [d10353, d53332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10355 q = 1) (hb : d53333 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10355, d53333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10355, d53333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d13675 q = 1) (hb : d53334 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13675, d53334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d13675, d53334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13676 q = 1) (hb : d53335 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13676, d53335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13676, d53335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d13678 q = 1) (hb : d53344 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13678, d53344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46928 q ha hb
    | true =>
      simp only [d13678, d53344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d13679 q = 1) (hb : d53345 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13679, d53345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13679, d53345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d13680 q = 1) (hb : d53346 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13680, d53346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d13680, d53346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d13681 q = 1) (hb : d53347 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13681, d53347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d13681, d53347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d13682 q = 1) (hb : d53348 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d13682, d53348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13682, d53348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d53348 q = 1) (hb : d196871 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d196871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d196871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro46930 (p : Pattern) (ha : d13677 p = 1) (hb : d69330 p = 1) : d0 p = 1 := by
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
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d69323 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d5715 q = 1) (hb : d69324 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d5715, d69324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5715, d69324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d53328 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d5716 q = 1) (hb : d69325 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d5716, d69325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5716, d69325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d5717 q = 1) (hb : d69326 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d5717, d69326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d5717, d69326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d69329 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d13677 q = 1) (hb : d69330 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d13677, d69330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d13677, d69330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro46931 (p : Pattern) (ha : d69335 p = 1) (hb : d196872 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d69335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d13678 q = 1) (hb : d69331 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13678, d69331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46930 q ha hb
    | true =>
      simp only [d13678, d69331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13679 q = 1) (hb : d69332 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13679, d69332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13679, d69332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d13680 q = 1) (hb : d69333 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13680, d69333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d13680, d69333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13681 q = 1) (hb : d69334 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13681, d69334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13681, d69334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d22693 q = 1) (hb : d69335 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22693, d69335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22693, d69335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d69335 q = 1) (hb : d196872 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d196872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d196872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  exact h7 p ha hb
theorem andIntro46932 (p : Pattern) (ha : d195897 p = 1) (hb : d196883 p = 1) : d197661 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d195893 q = 1) (hb : d196873 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d195893, d196873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46929 q ha hb
    | true =>
      simp only [d195893, d196873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46931 q ha hb
  have h2 (q : Pattern) (ha : d195894 q = 1) (hb : d196874 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d195894, d196874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195894, d196874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d195895 q = 1) (hb : d196875 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d195895, d196875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195895, d196875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d195895 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d195895 q = 1) (hb : d196876 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d196876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d196876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d1 q = 1) (hb : d196881 q = 1) : d196881 q = 1 := by
    exact hb
  have h7 (q : Pattern) (ha : d195896 q = 1) (hb : d196882 q = 1) : d197660 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d195896, d196882, d197660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d195896, d196882, d197660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d195897 q = 1) (hb : d196883 q = 1) : d197661 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d195897, d196883, d197661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d195897, d196883, d197661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro46933 (p : Pattern) (ha : d195903 p = 1) (hb : d196893 p = 1) : d197667 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d195898 q = 1) (hb : d196884 q = 1) : d197662 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d195898, d196884, d197662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46932 q ha hb
    | true =>
      simp only [d195898, d196884, d197662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d195899 q = 1) (hb : d196885 q = 1) : d197663 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d195899, d196885, d197663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195899, d196885, d197663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1 q = 1) (hb : d196889 q = 1) : d196889 q = 1 := by
    exact hb
  have h4 (q : Pattern) (ha : d195900 q = 1) (hb : d196890 q = 1) : d197664 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d195900, d196890, d197664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d195900, d196890, d197664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d195901 q = 1) (hb : d196891 q = 1) : d197665 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d195901, d196891, d197665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d195901, d196891, d197665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d195902 q = 1) (hb : d196892 q = 1) : d197666 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d195902, d196892, d197666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d195902, d196892, d197666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d195903 q = 1) (hb : d196893 q = 1) : d197667 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d195903, d196893, d197667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195903, d196893, d197667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro46934 (p : Pattern) (ha : d195909 p = 1) (hb : d196903 p = 1) : d197673 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d196897 q = 1) : d196897 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d195904 q = 1) (hb : d196898 q = 1) : d197668 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195904, d196898, d197668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46933 q ha hb
    | true =>
      simp only [d195904, d196898, d197668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d195905 q = 1) (hb : d196899 q = 1) : d197669 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d195905, d196899, d197669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195905, d196899, d197669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d195906 q = 1) (hb : d196900 q = 1) : d197670 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d195906, d196900, d197670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d195906, d196900, d197670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d195907 q = 1) (hb : d196901 q = 1) : d197671 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d195907, d196901, d197671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195907, d196901, d197671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d195908 q = 1) (hb : d196902 q = 1) : d197672 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d195908, d196902, d197672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195908, d196902, d197672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d195909 q = 1) (hb : d196903 q = 1) : d197673 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d195909, d196903, d197673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195909, d196903, d197673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro46935 (p : Pattern) (ha : d195912 p = 1) (hb : d196906 p = 1) : d197676 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d195898 q = 1) (hb : d196884 q = 1) : d197662 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d195898, d196884, d197662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46932 q ha hb
    | true =>
      simp only [d195898, d196884, d197662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d195899 q = 1) (hb : d196885 q = 1) : d197663 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d195899, d196885, d197663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195899, d196885, d197663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1 q = 1) (hb : d196889 q = 1) : d196889 q = 1 := by
    exact hb
  have h4 (q : Pattern) (ha : d195900 q = 1) (hb : d196890 q = 1) : d197664 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d195900, d196890, d197664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d195900, d196890, d197664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d195901 q = 1) (hb : d196891 q = 1) : d197665 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d195901, d196891, d197665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d195901, d196891, d197665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d195902 q = 1) (hb : d196892 q = 1) : d197666 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d195902, d196892, d197666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d195902, d196892, d197666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d195912 q = 1) (hb : d196906 q = 1) : d197676 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d195912, d196906, d197676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d195912, d196906, d197676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro46936 (p : Pattern) (ha : d195918 p = 1) (hb : d196913 p = 1) : d197682 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d196897 q = 1) : d196897 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d195904 q = 1) (hb : d196898 q = 1) : d197668 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195904, d196898, d197668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46933 q ha hb
    | true =>
      simp only [d195904, d196898, d197668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d195905 q = 1) (hb : d196899 q = 1) : d197669 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d195905, d196899, d197669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195905, d196899, d197669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d195906 q = 1) (hb : d196900 q = 1) : d197670 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d195906, d196900, d197670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d195906, d196900, d197670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d195907 q = 1) (hb : d196901 q = 1) : d197671 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d195907, d196901, d197671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195907, d196901, d197671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d195908 q = 1) (hb : d196902 q = 1) : d197672 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d195908, d196902, d197672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195908, d196902, d197672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1 q = 1) (hb : d196907 q = 1) : d196907 q = 1 := by
    exact hb
  have h8 (q : Pattern) (ha : d195913 q = 1) (hb : d196908 q = 1) : d197677 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195913, d196908, d197677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46935 q ha hb
    | true =>
      simp only [d195913, d196908, d197677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d195914 q = 1) (hb : d196909 q = 1) : d197678 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d195914, d196909, d197678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195914, d196909, d197678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d195915 q = 1) (hb : d196910 q = 1) : d197679 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d195915, d196910, d197679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d195915, d196910, d197679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d195916 q = 1) (hb : d196911 q = 1) : d197680 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d195916, d196911, d197680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195916, d196911, d197680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d195917 q = 1) (hb : d196912 q = 1) : d197681 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d195917, d196912, d197681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195917, d196912, d197681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d195918 q = 1) (hb : d196913 q = 1) : d197682 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d195918, d196913, d197682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d195918, d196913, d197682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro46937 (p : Pattern) (ha : d195897 p = 1) (hb : d196954 p = 1) : d197705 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d195893 q = 1) (hb : d196873 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d195893, d196873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46929 q ha hb
    | true =>
      simp only [d195893, d196873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46931 q ha hb
  have h2 (q : Pattern) (ha : d195894 q = 1) (hb : d196874 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d195894, d196874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195894, d196874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d195895 q = 1) (hb : d196875 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d195895, d196875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195895, d196875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d195895 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d195895 q = 1) (hb : d196876 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d196876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d196876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d1 q = 1) (hb : d196952 q = 1) : d196952 q = 1 := by
    exact hb
  have h7 (q : Pattern) (ha : d195896 q = 1) (hb : d196953 q = 1) : d197704 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d195896, d196953, d197704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d195896, d196953, d197704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d195897 q = 1) (hb : d196954 q = 1) : d197705 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d195897, d196954, d197705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d195897, d196954, d197705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro46938 (p : Pattern) (ha : d195903 p = 1) (hb : d196960 p = 1) : d197711 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d195898 q = 1) (hb : d196955 q = 1) : d197706 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d195898, d196955, d197706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46937 q ha hb
    | true =>
      simp only [d195898, d196955, d197706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d195899 q = 1) (hb : d196956 q = 1) : d197707 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d195899, d196956, d197707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195899, d196956, d197707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d195900 q = 1) (hb : d196957 q = 1) : d197708 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d195900, d196957, d197708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d195900, d196957, d197708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d195901 q = 1) (hb : d196958 q = 1) : d197709 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d195901, d196958, d197709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d195901, d196958, d197709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d195902 q = 1) (hb : d196959 q = 1) : d197710 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d195902, d196959, d197710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d195902, d196959, d197710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d195903 q = 1) (hb : d196960 q = 1) : d197711 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d195903, d196960, d197711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195903, d196960, d197711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro46939 (p : Pattern) (ha : d195923 p = 1) (hb : d196918 p = 1) : d197687 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d195898 q = 1) (hb : d196884 q = 1) : d197662 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d195898, d196884, d197662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46932 q ha hb
    | true =>
      simp only [d195898, d196884, d197662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d195899 q = 1) (hb : d196885 q = 1) : d197663 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d195899, d196885, d197663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195899, d196885, d197663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1 q = 1) (hb : d196889 q = 1) : d196889 q = 1 := by
    exact hb
  have h4 (q : Pattern) (ha : d195900 q = 1) (hb : d196890 q = 1) : d197664 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d195900, d196890, d197664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d195900, d196890, d197664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d195901 q = 1) (hb : d196891 q = 1) : d197665 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d195901, d196891, d197665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d195901, d196891, d197665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d195922 q = 1) (hb : d196917 q = 1) : d197686 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d195922, d196917, d197686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195922, d196917, d197686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d195923 q = 1) (hb : d196918 q = 1) : d197687 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d195923, d196918, d197687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195923, d196918, d197687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro46940 (p : Pattern) (ha : d195930 p = 1) (hb : d196927 p = 1) : d197694 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d195898 q = 1) (hb : d196884 q = 1) : d197662 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d195898, d196884, d197662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46932 q ha hb
    | true =>
      simp only [d195898, d196884, d197662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d195899 q = 1) (hb : d196885 q = 1) : d197663 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d195899, d196885, d197663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195899, d196885, d197663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1 q = 1) (hb : d196889 q = 1) : d196889 q = 1 := by
    exact hb
  have h4 (q : Pattern) (ha : d195900 q = 1) (hb : d196890 q = 1) : d197664 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d195900, d196890, d197664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d195900, d196890, d197664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d195928 q = 1) (hb : d196925 q = 1) : d197692 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d195928, d196925, d197692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195928, d196925, d197692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d195929 q = 1) (hb : d196926 q = 1) : d197693 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d195929, d196926, d197693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d195929, d196926, d197693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d195930 q = 1) (hb : d196927 q = 1) : d197694 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d195930, d196927, d197694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195930, d196927, d197694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro46941 (p : Pattern) (ha : d53336 p = 1) (hb : d196934 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53336 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53317 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d10353 q = 1) (hb : d53332 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10353, d53332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35680 q ha hb
    | true =>
      simp only [d10353, d53332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10355 q = 1) (hb : d53333 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10355, d53333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10355, d53333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h5 (q : Pattern) (ha : d13675 q = 1) (hb : d53334 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13675, d53334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13675, d53334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13676 q = 1) (hb : d53335 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13676, d53335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13676, d53335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h7 (q : Pattern) (ha : d17228 q = 1) (hb : d53336 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17228, d53336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d17228, d53336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d53336 q = 1) (hb : d196934 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d196934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d196934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro46942 (p : Pattern) (ha : d113872 p = 1) (hb : d196871 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d113872 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10353 q = 1) (hb : d101674 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10353, d101674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23367 q ha hb
    | true =>
      simp only [d10353, d101674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10355 q = 1) (hb : d101676 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10355, d101676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10355, d101676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d13675 q = 1) (hb : d113865 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13675, d113865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d13675, d113865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13676 q = 1) (hb : d113866 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13676, d113866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13676, d113866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d13678 q = 1) (hb : d113868 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13678, d113868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29873 q ha hb
    | true =>
      simp only [d13678, d113868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d13679 q = 1) (hb : d113869 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13679, d113869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13679, d113869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d13680 q = 1) (hb : d113870 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13680, d113870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d13680, d113870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d13681 q = 1) (hb : d113871 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13681, d113871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d13681, d113871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d13682 q = 1) (hb : d113872 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d13682, d113872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13682, d113872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d113872 q = 1) (hb : d196871 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d196871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d196871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro46943 (p : Pattern) (ha : d195938 p = 1) (hb : d196940 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d195934 q = 1) (hb : d196935 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d195934, d196935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46941 q ha hb
    | true =>
      simp only [d195934, d196935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46942 q ha hb
  have h2 (q : Pattern) (ha : d195935 q = 1) (hb : d196936 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d195935, d196936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195935, d196936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d195936 q = 1) (hb : d196937 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d195936, d196937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195936, d196937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d195936 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d195936 q = 1) (hb : d196938 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d196938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d196938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d195893 q = 1) (hb : d196873 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d195893, d196873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46929 q ha hb
    | true =>
      simp only [d195893, d196873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46931 q ha hb
  have h7 (q : Pattern) (ha : d195894 q = 1) (hb : d196874 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d195894, d196874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195894, d196874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d195895 q = 1) (hb : d196875 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d195895, d196875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195895, d196875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d195895 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d195895 q = 1) (hb : d196876 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d196876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d196876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d195937 q = 1) (hb : d196939 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d195937, d196939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d195937, d196939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d195938 q = 1) (hb : d196940 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d195938, d196940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d195938, d196940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h12 p ha hb
theorem andIntro46944 (p : Pattern) (ha : d195944 p = 1) (hb : d196946 p = 1) : d197701 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d195939 q = 1) (hb : d196941 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d195939, d196941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46943 q ha hb
    | true =>
      simp only [d195939, d196941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d195940 q = 1) (hb : d196942 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d195940, d196942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195940, d196942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d195898 q = 1) (hb : d196884 q = 1) : d197662 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d195898, d196884, d197662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46932 q ha hb
    | true =>
      simp only [d195898, d196884, d197662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d195899 q = 1) (hb : d196885 q = 1) : d197663 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d195899, d196885, d197663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195899, d196885, d197663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d195941 q = 1) (hb : d196943 q = 1) : d197698 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d195941, d196943, d197698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d195941, d196943, d197698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d195942 q = 1) (hb : d196944 q = 1) : d197699 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d195942, d196944, d197699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d195942, d196944, d197699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d195943 q = 1) (hb : d196945 q = 1) : d197700 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d195943, d196945, d197700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d195943, d196945, d197700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d195944 q = 1) (hb : d196946 q = 1) : d197701 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d195944, d196946, d197701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195944, d196946, d197701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro46945 (p : Pattern) (ha : d195951 p = 1) (hb : d196966 p = 1) : d197717 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d196920 q = 1) : d196920 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d195924 q = 1) (hb : d196921 q = 1) : d197688 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195924, d196921, d197688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46939 q ha hb
    | true =>
      simp only [d195924, d196921, d197688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d195925 q = 1) (hb : d196922 q = 1) : d197689 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d195925, d196922, d197689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195925, d196922, d197689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d195926 q = 1) (hb : d196923 q = 1) : d197690 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d195926, d196923, d197690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d195926, d196923, d197690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d195927 q = 1) (hb : d196924 q = 1) : d197691 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d195927, d196924, d197691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195927, d196924, d197691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1 q = 1) (hb : d196930 q = 1) : d196930 q = 1 := by
    exact hb
  have h7 (q : Pattern) (ha : d195931 q = 1) (hb : d196931 q = 1) : d197695 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195931, d196931, d197695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46940 q ha hb
    | true =>
      simp only [d195931, d196931, d197695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d195932 q = 1) (hb : d196932 q = 1) : d197696 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d195932, d196932, d197696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195932, d196932, d197696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d195933 q = 1) (hb : d196933 q = 1) : d197697 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d195933, d196933, d197697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d195933, d196933, d197697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d195945 q = 1) (hb : d196947 q = 1) : d197702 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195945, d196947, d197702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46944 q ha hb
    | true =>
      simp only [d195945, d196947, d197702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46933 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d195904 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d195946 q = 1) (hb : d196948 q = 1) : d197703 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d195946, d196948, d197703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d195946, d196948, d197703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d195904 q = 1) (hb : d196961 q = 1) : d197712 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195904, d196961, d197712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46938 q ha hb
    | true =>
      simp only [d195904, d196961, d197712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d195947 q = 1) (hb : d196962 q = 1) : d197713 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d195947, d196962, d197713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d195947, d196962, d197713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d195948 q = 1) (hb : d196963 q = 1) : d197714 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d195948, d196963, d197714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d195948, d196963, d197714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d195949 q = 1) (hb : d196964 q = 1) : d197715 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d195949, d196964, d197715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d195949, d196964, d197715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d195950 q = 1) (hb : d196965 q = 1) : d197716 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d195950, d196965, d197716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d195950, d196965, d197716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d195951 q = 1) (hb : d196966 q = 1) : d197717 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d195951, d196966, d197717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195951, d196966, d197717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro46946 (p : Pattern) (ha : d195912 p = 1) (hb : d196981 p = 1) : d197730 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d195898 q = 1) (hb : d196955 q = 1) : d197706 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d195898, d196955, d197706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46937 q ha hb
    | true =>
      simp only [d195898, d196955, d197706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d195899 q = 1) (hb : d196956 q = 1) : d197707 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d195899, d196956, d197707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195899, d196956, d197707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d195900 q = 1) (hb : d196957 q = 1) : d197708 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d195900, d196957, d197708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d195900, d196957, d197708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d195901 q = 1) (hb : d196958 q = 1) : d197709 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d195901, d196958, d197709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d195901, d196958, d197709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d195902 q = 1) (hb : d196959 q = 1) : d197710 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d195902, d196959, d197710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d195902, d196959, d197710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d195912 q = 1) (hb : d196981 q = 1) : d197730 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d195912, d196981, d197730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d195912, d196981, d197730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro46947 (p : Pattern) (ha : d195952 p = 1) (hb : d196967 p = 1) : d197718 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d195898 q = 1) (hb : d196884 q = 1) : d197662 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d195898, d196884, d197662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46932 q ha hb
    | true =>
      simp only [d195898, d196884, d197662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d195899 q = 1) (hb : d196885 q = 1) : d197663 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d195899, d196885, d197663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195899, d196885, d197663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1 q = 1) (hb : d196889 q = 1) : d196889 q = 1 := by
    exact hb
  have h4 (q : Pattern) (ha : d195900 q = 1) (hb : d196890 q = 1) : d197664 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d195900, d196890, d197664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d195900, d196890, d197664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d195901 q = 1) (hb : d196891 q = 1) : d197665 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d195901, d196891, d197665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d195901, d196891, d197665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d195922 q = 1) (hb : d196917 q = 1) : d197686 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d195922, d196917, d197686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195922, d196917, d197686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d195952 q = 1) (hb : d196967 q = 1) : d197718 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d195952, d196967, d197718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d195952, d196967, d197718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro46948 (p : Pattern) (ha : d195957 p = 1) (hb : d196973 p = 1) : d197723 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d195898 q = 1) (hb : d196884 q = 1) : d197662 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d195898, d196884, d197662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46932 q ha hb
    | true =>
      simp only [d195898, d196884, d197662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d195899 q = 1) (hb : d196885 q = 1) : d197663 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d195899, d196885, d197663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195899, d196885, d197663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1 q = 1) (hb : d196889 q = 1) : d196889 q = 1 := by
    exact hb
  have h4 (q : Pattern) (ha : d195900 q = 1) (hb : d196890 q = 1) : d197664 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d195900, d196890, d197664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d195900, d196890, d197664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d195928 q = 1) (hb : d196925 q = 1) : d197692 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d195928, d196925, d197692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195928, d196925, d197692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d195929 q = 1) (hb : d196926 q = 1) : d197693 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d195929, d196926, d197693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d195929, d196926, d197693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d195957 q = 1) (hb : d196973 q = 1) : d197723 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d195957, d196973, d197723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d195957, d196973, d197723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro46949 (p : Pattern) (ha : d195961 p = 1) (hb : d196978 p = 1) : d197727 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d195939 q = 1) (hb : d196941 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d195939, d196941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46943 q ha hb
    | true =>
      simp only [d195939, d196941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d195940 q = 1) (hb : d196942 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d195940, d196942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195940, d196942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d195898 q = 1) (hb : d196884 q = 1) : d197662 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d195898, d196884, d197662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46932 q ha hb
    | true =>
      simp only [d195898, d196884, d197662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d195899 q = 1) (hb : d196885 q = 1) : d197663 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d195899, d196885, d197663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195899, d196885, d197663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d195941 q = 1) (hb : d196943 q = 1) : d197698 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d195941, d196943, d197698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d195941, d196943, d197698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d195942 q = 1) (hb : d196944 q = 1) : d197699 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d195942, d196944, d197699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d195942, d196944, d197699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d195943 q = 1) (hb : d196945 q = 1) : d197700 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d195943, d196945, d197700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d195943, d196945, d197700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d195961 q = 1) (hb : d196978 q = 1) : d197727 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d195961, d196978, d197727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d195961, d196978, d197727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro46950 (p : Pattern) (ha : d195968 p = 1) (hb : d196987 p = 1) : d197736 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d196920 q = 1) : d196920 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d195924 q = 1) (hb : d196921 q = 1) : d197688 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195924, d196921, d197688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46939 q ha hb
    | true =>
      simp only [d195924, d196921, d197688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d195925 q = 1) (hb : d196922 q = 1) : d197689 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d195925, d196922, d197689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195925, d196922, d197689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d195926 q = 1) (hb : d196923 q = 1) : d197690 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d195926, d196923, d197690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d195926, d196923, d197690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d195927 q = 1) (hb : d196924 q = 1) : d197691 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d195927, d196924, d197691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195927, d196924, d197691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1 q = 1) (hb : d196930 q = 1) : d196930 q = 1 := by
    exact hb
  have h7 (q : Pattern) (ha : d195931 q = 1) (hb : d196931 q = 1) : d197695 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195931, d196931, d197695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46940 q ha hb
    | true =>
      simp only [d195931, d196931, d197695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d195932 q = 1) (hb : d196932 q = 1) : d197696 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d195932, d196932, d197696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195932, d196932, d197696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d195933 q = 1) (hb : d196933 q = 1) : d197697 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d195933, d196933, d197697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d195933, d196933, d197697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d195945 q = 1) (hb : d196947 q = 1) : d197702 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195945, d196947, d197702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46944 q ha hb
    | true =>
      simp only [d195945, d196947, d197702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46933 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d195904 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d195946 q = 1) (hb : d196948 q = 1) : d197703 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d195946, d196948, d197703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d195946, d196948, d197703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d195904 q = 1) (hb : d196961 q = 1) : d197712 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195904, d196961, d197712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46938 q ha hb
    | true =>
      simp only [d195904, d196961, d197712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d195947 q = 1) (hb : d196962 q = 1) : d197713 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d195947, d196962, d197713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d195947, d196962, d197713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d195948 q = 1) (hb : d196963 q = 1) : d197714 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d195948, d196963, d197714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d195948, d196963, d197714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d195949 q = 1) (hb : d196964 q = 1) : d197715 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d195949, d196964, d197715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d195949, d196964, d197715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d195950 q = 1) (hb : d196965 q = 1) : d197716 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d195950, d196965, d197716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d195950, d196965, d197716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d1 q = 1) (hb : d196968 q = 1) : d196968 q = 1 := by
    exact hb
  have h19 (q : Pattern) (ha : d195953 q = 1) (hb : d196969 q = 1) : d197719 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195953, d196969, d197719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46947 q ha hb
    | true =>
      simp only [d195953, d196969, d197719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d195954 q = 1) (hb : d196970 q = 1) : d197720 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d195954, d196970, d197720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195954, d196970, d197720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d195955 q = 1) (hb : d196971 q = 1) : d197721 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d195955, d196971, d197721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d195955, d196971, d197721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d195956 q = 1) (hb : d196972 q = 1) : d197722 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d195956, d196972, d197722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195956, d196972, d197722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d1 q = 1) (hb : d196974 q = 1) : d196974 q = 1 := by
    exact hb
  have h24 (q : Pattern) (ha : d195958 q = 1) (hb : d196975 q = 1) : d197724 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195958, d196975, d197724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46948 q ha hb
    | true =>
      simp only [d195958, d196975, d197724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d195959 q = 1) (hb : d196976 q = 1) : d197725 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d195959, d196976, d197725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195959, d196976, d197725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
  have h26 (q : Pattern) (ha : d195960 q = 1) (hb : d196977 q = 1) : d197726 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d195960, d196977, d197726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d195960, d196977, d197726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d195962 q = 1) (hb : d196979 q = 1) : d197728 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195962, d196979, d197728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46949 q ha hb
    | true =>
      simp only [d195962, d196979, d197728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46935 q ha hb
  have h28 (q : Pattern) (ha : d0 q = 1) (hb : d195913 q = 1) : d0 q = 1 := by
    exact ha
  have h29 (q : Pattern) (ha : d195963 q = 1) (hb : d196980 q = 1) : d197729 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d195963, d196980, d197729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
    | true =>
      simp only [d195963, d196980, d197729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q hb ha
  have h30 (q : Pattern) (ha : d195913 q = 1) (hb : d196982 q = 1) : d197731 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195913, d196982, d197731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46946 q ha hb
    | true =>
      simp only [d195913, d196982, d197731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h31 (q : Pattern) (ha : d195964 q = 1) (hb : d196983 q = 1) : d197732 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d195964, d196983, d197732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
    | true =>
      simp only [d195964, d196983, d197732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h32 (q : Pattern) (ha : d195965 q = 1) (hb : d196984 q = 1) : d197733 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d195965, d196984, d197733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
    | true =>
      simp only [d195965, d196984, d197733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
  have h33 (q : Pattern) (ha : d195966 q = 1) (hb : d196985 q = 1) : d197734 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d195966, d196985, d197734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d195966, d196985, d197734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h32 q ha hb
  have h34 (q : Pattern) (ha : d195967 q = 1) (hb : d196986 q = 1) : d197735 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d195967, d196986, d197735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d195967, d196986, d197735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h33 q ha hb
  have h35 (q : Pattern) (ha : d195968 q = 1) (hb : d196987 q = 1) : d197736 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d195968, d196987, d197736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d195968, d196987, d197736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h34 q ha hb
  exact h35 p ha hb
theorem andIntro46951 (p : Pattern) (ha : d195970 p = 1) (hb : d196994 p = 1) : d197738 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d196897 q = 1) : d196897 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d195904 q = 1) (hb : d196898 q = 1) : d197668 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195904, d196898, d197668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46933 q ha hb
    | true =>
      simp only [d195904, d196898, d197668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d195905 q = 1) (hb : d196899 q = 1) : d197669 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d195905, d196899, d197669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195905, d196899, d197669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d195906 q = 1) (hb : d196900 q = 1) : d197670 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d195906, d196900, d197670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d195906, d196900, d197670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d195907 q = 1) (hb : d196901 q = 1) : d197671 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d195907, d196901, d197671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195907, d196901, d197671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d195908 q = 1) (hb : d196902 q = 1) : d197672 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d195908, d196902, d197672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195908, d196902, d197672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1 q = 1) (hb : d196993 q = 1) : d196993 q = 1 := by
    exact hb
  have h8 (q : Pattern) (ha : d195970 q = 1) (hb : d196994 q = 1) : d197738 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d195970, d196994, d197738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d195970, d196994, d197738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro46952 (p : Pattern) (ha : d195977 p = 1) (hb : d197007 p = 1) : d197745 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d195962 q = 1) (hb : d196979 q = 1) : d197728 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195962, d196979, d197728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46949 q ha hb
    | true =>
      simp only [d195962, d196979, d197728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46935 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d195913 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d195963 q = 1) (hb : d196980 q = 1) : d197729 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d195963, d196980, d197729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d195963, d196980, d197729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d195913 q = 1) (hb : d196982 q = 1) : d197731 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195913, d196982, d197731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46946 q ha hb
    | true =>
      simp only [d195913, d196982, d197731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d195964 q = 1) (hb : d196983 q = 1) : d197732 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d195964, d196983, d197732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d195964, d196983, d197732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d195965 q = 1) (hb : d196984 q = 1) : d197733 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d195965, d196984, d197733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d195965, d196984, d197733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d195975 q = 1) (hb : d197005 q = 1) : d197743 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d195975, d197005, d197743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195975, d197005, d197743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d195976 q = 1) (hb : d197006 q = 1) : d197744 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d195976, d197006, d197744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195976, d197006, d197744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d195977 q = 1) (hb : d197007 q = 1) : d197745 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d195977, d197007, d197745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195977, d197007, d197745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro46953 (p : Pattern) (ha : d53509 p = 1) (hb : d197015 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53509 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53503 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d13813 q = 1) (hb : d53505 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13813, d53505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13813, d53505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35680 q ha hb
  have h4 (q : Pattern) (ha : d10353 q = 1) (hb : d53332 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10353, d53332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35680 q ha hb
    | true =>
      simp only [d10353, d53332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h5 (q : Pattern) (ha : d13814 q = 1) (hb : d53506 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13814, d53506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13814, d53506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10355 q = 1) (hb : d53333 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10355, d53333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10355, d53333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h7 (q : Pattern) (ha : d13815 q = 1) (hb : d53507 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13815, d53507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13815, d53507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d13816 q = 1) (hb : d53508 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13816, d53508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13816, d53508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h9 (q : Pattern) (ha : d17374 q = 1) (hb : d53509 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17374, d53509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d17374, d53509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53509 q = 1) (hb : d197015 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d197015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d197015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  exact h10 p ha hb
theorem andIntro46954 (p : Pattern) (ha : d53515 p = 1) (hb : d197016 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53515 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d13813 q = 1) (hb : d53505 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13813, d53505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d13813, d53505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35680 q ha hb
  have h3 (q : Pattern) (ha : d10353 q = 1) (hb : d53332 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10353, d53332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35680 q ha hb
    | true =>
      simp only [d10353, d53332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d13814 q = 1) (hb : d53506 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13814, d53506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13814, d53506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10355 q = 1) (hb : d53333 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10355, d53333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10355, d53333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d13815 q = 1) (hb : d53507 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13815, d53507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13815, d53507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d13816 q = 1) (hb : d53508 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13816, d53508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13816, d53508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d13817 q = 1) (hb : d53511 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13817, d53511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d13817, d53511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46928 q ha hb
  have h9 (q : Pattern) (ha : d13678 q = 1) (hb : d53344 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13678, d53344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46928 q ha hb
    | true =>
      simp only [d13678, d53344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d13818 q = 1) (hb : d53512 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13818, d53512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d13818, d53512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d13679 q = 1) (hb : d53345 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13679, d53345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d13679, d53345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h12 (q : Pattern) (ha : d13819 q = 1) (hb : d53513 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13819, d53513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d13819, d53513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d13820 q = 1) (hb : d53514 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13820, d53514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d13820, d53514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h14 (q : Pattern) (ha : d13821 q = 1) (hb : d53515 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d13821, d53515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13821, d53515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d53515 q = 1) (hb : d197016 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d197016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d197016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  exact h15 p ha hb
theorem andIntro46955 (p : Pattern) (ha : d76365 p = 1) (hb : d197021 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d76365 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d13817 q = 1) (hb : d76361 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13817, d76361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d13817, d76361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46930 q ha hb
  have h3 (q : Pattern) (ha : d13678 q = 1) (hb : d69331 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13678, d69331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46930 q ha hb
    | true =>
      simp only [d13678, d69331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d13818 q = 1) (hb : d76362 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13818, d76362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13818, d76362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13679 q = 1) (hb : d69332 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13679, d69332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13679, d69332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d13819 q = 1) (hb : d76363 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13819, d76363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13819, d76363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d13820 q = 1) (hb : d76364 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13820, d76364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13820, d76364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d22937 q = 1) (hb : d76365 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22937, d76365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22937, d76365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h9 (q : Pattern) (ha : d76365 q = 1) (hb : d197021 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d197021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d197021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  exact h9 p ha hb
theorem andIntro46956 (p : Pattern) (ha : d113973 p = 1) (hb : d197016 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d113973 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d13813 q = 1) (hb : d113965 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13813, d113965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d13813, d113965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23367 q ha hb
  have h3 (q : Pattern) (ha : d10353 q = 1) (hb : d101674 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10353, d101674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23367 q ha hb
    | true =>
      simp only [d10353, d101674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d13814 q = 1) (hb : d113966 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13814, d113966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13814, d113966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10355 q = 1) (hb : d101676 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10355, d101676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10355, d101676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d13815 q = 1) (hb : d113967 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13815, d113967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13815, d113967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d13816 q = 1) (hb : d113968 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13816, d113968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13816, d113968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d13817 q = 1) (hb : d113969 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13817, d113969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d13817, d113969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29873 q ha hb
  have h9 (q : Pattern) (ha : d13678 q = 1) (hb : d113868 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13678, d113868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29873 q ha hb
    | true =>
      simp only [d13678, d113868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d13818 q = 1) (hb : d113970 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13818, d113970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d13818, d113970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d13679 q = 1) (hb : d113869 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13679, d113869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d13679, d113869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h12 (q : Pattern) (ha : d13819 q = 1) (hb : d113971 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13819, d113971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d13819, d113971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d13820 q = 1) (hb : d113972 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13820, d113972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d13820, d113972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h14 (q : Pattern) (ha : d13821 q = 1) (hb : d113973 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d13821, d113973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13821, d113973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d113973 q = 1) (hb : d197016 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d197016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d197016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  exact h15 p ha hb
theorem andIntro46957 (p : Pattern) (ha : d195990 p = 1) (hb : d197027 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d195983 q = 1) (hb : d197017 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d195983, d197017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46953 q ha hb
    | true =>
      simp only [d195983, d197017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46956 q ha hb
  have h2 (q : Pattern) (ha : d195984 q = 1) (hb : d197018 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d195984, d197018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195984, d197018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d195985 q = 1) (hb : d197019 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d195985, d197019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195985, d197019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d195985 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d195985 q = 1) (hb : d197020 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d197020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d197020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d195986 q = 1) (hb : d197022 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d195986, d197022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46954 q ha hb
    | true =>
      simp only [d195986, d197022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46955 q ha hb
  have h7 (q : Pattern) (ha : d195987 q = 1) (hb : d197023 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d195987, d197023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195987, d197023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d195988 q = 1) (hb : d197024 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d195988, d197024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195988, d197024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d195988 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d195988 q = 1) (hb : d197025 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d197025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d197025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d195989 q = 1) (hb : d197026 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d195989, d197026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d195989, d197026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d195990 q = 1) (hb : d197027 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d195990, d197027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d195990, d197027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h12 p ha hb
theorem andIntro46958 (p : Pattern) (ha : d195994 p = 1) (hb : d197036 p = 1) : d197752 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d195986 q = 1) (hb : d197022 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d195986, d197022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46954 q ha hb
    | true =>
      simp only [d195986, d197022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46955 q ha hb
  have h2 (q : Pattern) (ha : d195987 q = 1) (hb : d197023 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d195987, d197023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195987, d197023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d195988 q = 1) (hb : d197024 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d195988, d197024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195988, d197024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d195988 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d195988 q = 1) (hb : d197025 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d197025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d197025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d1 q = 1) (hb : d197034 q = 1) : d197034 q = 1 := by
    exact hb
  have h7 (q : Pattern) (ha : d195993 q = 1) (hb : d197035 q = 1) : d197751 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d195993, d197035, d197751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d195993, d197035, d197751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d195994 q = 1) (hb : d197036 q = 1) : d197752 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d195994, d197036, d197752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d195994, d197036, d197752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro46959 (p : Pattern) (ha : d196000 p = 1) (hb : d197042 p = 1) : d197758 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d195991 q = 1) (hb : d197028 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d195991, d197028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46957 q ha hb
    | true =>
      simp only [d195991, d197028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d195992 q = 1) (hb : d197029 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d195992, d197029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195992, d197029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d195995 q = 1) (hb : d197037 q = 1) : d197753 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d195995, d197037, d197753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46958 q ha hb
    | true =>
      simp only [d195995, d197037, d197753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d195996 q = 1) (hb : d197038 q = 1) : d197754 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d195996, d197038, d197754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195996, d197038, d197754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d195997 q = 1) (hb : d197039 q = 1) : d197755 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d195997, d197039, d197755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d195997, d197039, d197755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d195998 q = 1) (hb : d197040 q = 1) : d197756 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d195998, d197040, d197756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d195998, d197040, d197756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d195999 q = 1) (hb : d197041 q = 1) : d197757 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d195999, d197041, d197757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d195999, d197041, d197757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d196000 q = 1) (hb : d197042 q = 1) : d197758 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d196000, d197042, d197758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d196000, d197042, d197758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro46960 (p : Pattern) (ha : d196004 p = 1) (hb : d197050 p = 1) : d197762 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d195995 q = 1) (hb : d197037 q = 1) : d197753 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d195995, d197037, d197753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46958 q ha hb
    | true =>
      simp only [d195995, d197037, d197753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d195996 q = 1) (hb : d197038 q = 1) : d197754 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d195996, d197038, d197754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195996, d197038, d197754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1 q = 1) (hb : d197046 q = 1) : d197046 q = 1 := by
    exact hb
  have h4 (q : Pattern) (ha : d196001 q = 1) (hb : d197047 q = 1) : d197759 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d196001, d197047, d197759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d196001, d197047, d197759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d196002 q = 1) (hb : d197048 q = 1) : d197760 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d196002, d197048, d197760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d196002, d197048, d197760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d196003 q = 1) (hb : d197049 q = 1) : d197761 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d196003, d197049, d197761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d196003, d197049, d197761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d196004 q = 1) (hb : d197050 q = 1) : d197762 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d196004, d197050, d197762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d196004, d197050, d197762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro46961 (p : Pattern) (ha : d195994 p = 1) (hb : d197058 p = 1) : d197766 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d195986 q = 1) (hb : d197022 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d195986, d197022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46954 q ha hb
    | true =>
      simp only [d195986, d197022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46955 q ha hb
  have h2 (q : Pattern) (ha : d195987 q = 1) (hb : d197023 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d195987, d197023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195987, d197023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d195988 q = 1) (hb : d197024 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d195988, d197024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195988, d197024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d195988 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d195988 q = 1) (hb : d197025 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d197025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d197025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d1 q = 1) (hb : d197056 q = 1) : d197056 q = 1 := by
    exact hb
  have h7 (q : Pattern) (ha : d195993 q = 1) (hb : d197057 q = 1) : d197765 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d195993, d197057, d197765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d195993, d197057, d197765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d195994 q = 1) (hb : d197058 q = 1) : d197766 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d195994, d197058, d197766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d195994, d197058, d197766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro46962 (p : Pattern) (ha : d196004 p = 1) (hb : d197064 p = 1) : d197772 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d195995 q = 1) (hb : d197059 q = 1) : d197767 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d195995, d197059, d197767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46961 q ha hb
    | true =>
      simp only [d195995, d197059, d197767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d195996 q = 1) (hb : d197060 q = 1) : d197768 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d195996, d197060, d197768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195996, d197060, d197768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d196001 q = 1) (hb : d197061 q = 1) : d197769 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d196001, d197061, d197769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d196001, d197061, d197769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d196002 q = 1) (hb : d197062 q = 1) : d197770 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d196002, d197062, d197770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d196002, d197062, d197770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d196003 q = 1) (hb : d197063 q = 1) : d197771 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d196003, d197063, d197771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d196003, d197063, d197771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d196004 q = 1) (hb : d197064 q = 1) : d197772 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d196004, d197064, d197772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d196004, d197064, d197772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro46963 (p : Pattern) (ha : d196012 p = 1) (hb : d197070 p = 1) : d197778 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d196005 q = 1) (hb : d197051 q = 1) : d197763 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d196005, d197051, d197763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46959 q ha hb
    | true =>
      simp only [d196005, d197051, d197763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46960 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d196006 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d196007 q = 1) (hb : d197052 q = 1) : d197764 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d196007, d197052, d197764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d196007, d197052, d197764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d196006 q = 1) (hb : d197065 q = 1) : d197773 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d196006, d197065, d197773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46962 q ha hb
    | true =>
      simp only [d196006, d197065, d197773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d196008 q = 1) (hb : d197066 q = 1) : d197774 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d196008, d197066, d197774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d196008, d197066, d197774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d196009 q = 1) (hb : d197067 q = 1) : d197775 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d196009, d197067, d197775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d196009, d197067, d197775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d196010 q = 1) (hb : d197068 q = 1) : d197776 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d196010, d197068, d197776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d196010, d197068, d197776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d196011 q = 1) (hb : d197069 q = 1) : d197777 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d196011, d197069, d197777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d196011, d197069, d197777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d196012 q = 1) (hb : d197070 q = 1) : d197778 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d196012, d197070, d197778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d196012, d197070, d197778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro46964 (p : Pattern) (ha : d196018 p = 1) (hb : d197087 p = 1) : d197784 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d195910 q = 1) (hb : d196904 q = 1) : d197674 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d195910, d196904, d197674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195910, d196904, d197674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46934 q ha hb
  have h2 (q : Pattern) (ha : d195911 q = 1) (hb : d196905 q = 1) : d197675 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d195911, d196905, d197675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d195911, d196905, d197675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d195919 q = 1) (hb : d196914 q = 1) : d197683 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d195919, d196914, d197683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46934 q ha hb
    | true =>
      simp only [d195919, d196914, d197683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46936 q ha hb
  have h4 (q : Pattern) (ha : d195920 q = 1) (hb : d196915 q = 1) : d197684 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d195920, d196915, d197684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d195920, d196915, d197684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d195921 q = 1) (hb : d196916 q = 1) : d197685 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d195921, d196916, d197685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d195921, d196916, d197685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d195969 q = 1) (hb : d196988 q = 1) : d197737 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d195969, d196988, d197737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46945 q ha hb
    | true =>
      simp only [d195969, d196988, d197737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46950 q ha hb
  have h7 (q : Pattern) (ha : d1 q = 1) (hb : d197000 q = 1) : d197000 q = 1 := by
    exact hb
  have h8 (q : Pattern) (ha : d195971 q = 1) (hb : d197001 q = 1) : d197739 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d195971, d197001, d197739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46951 q ha hb
    | true =>
      simp only [d195971, d197001, d197739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d195972 q = 1) (hb : d197002 q = 1) : d197740 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d195972, d197002, d197740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d195972, d197002, d197740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d195973 q = 1) (hb : d197003 q = 1) : d197741 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d195973, d197003, d197741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d195973, d197003, d197741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d195974 q = 1) (hb : d197004 q = 1) : d197742 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d195974, d197004, d197742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d195974, d197004, d197742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d195978 q = 1) (hb : d197008 q = 1) : d197746 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d195978, d197008, d197746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d195978, d197008, d197746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46952 q ha hb
  have h13 (q : Pattern) (ha : d1 q = 1) (hb : d197010 q = 1) : d197010 q = 1 := by
    exact hb
  have h14 (q : Pattern) (ha : d195979 q = 1) (hb : d197011 q = 1) : d197747 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d195979, d197011, d197747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d195979, d197011, d197747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d195980 q = 1) (hb : d197012 q = 1) : d197748 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d195980, d197012, d197748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d195980, d197012, d197748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d195981 q = 1) (hb : d197013 q = 1) : d197749 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d195981, d197013, d197749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d195981, d197013, d197749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h17 (q : Pattern) (ha : d195982 q = 1) (hb : d197014 q = 1) : d197750 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d195982, d197014, d197750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d195982, d197014, d197750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d196013 q = 1) (hb : d197071 q = 1) : d197779 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d196013, d197071, d197779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d196013, d197071, d197779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46963 q ha hb
  have h19 (q : Pattern) (ha : d1 q = 1) (hb : d197082 q = 1) : d197082 q = 1 := by
    exact hb
  have h20 (q : Pattern) (ha : d196014 q = 1) (hb : d197083 q = 1) : d197780 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d196014, d197083, d197780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d196014, d197083, d197780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d196015 q = 1) (hb : d197084 q = 1) : d197781 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d196015, d197084, d197781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d196015, d197084, d197781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d196016 q = 1) (hb : d197085 q = 1) : d197782 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d196016, d197085, d197782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d196016, d197085, d197782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d196017 q = 1) (hb : d197086 q = 1) : d197783 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d196017, d197086, d197783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d196017, d197086, d197783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d196018 q = 1) (hb : d197087 q = 1) : d197784 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d196018, d197087, d197784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d196018, d197087, d197784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  exact h24 p ha hb
theorem andIntro46965 (p : Pattern) (ha : d196024 p = 1) (hb : d197093 p = 1) : d197790 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d196019 q = 1) (hb : d197088 q = 1) : d197785 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d196019, d197088, d197785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d196019, d197088, d197785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46964 q ha hb
  have h2 (q : Pattern) (ha : d196020 q = 1) (hb : d197089 q = 1) : d197786 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d196020, d197089, d197786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d196020, d197089, d197786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d196021 q = 1) (hb : d197090 q = 1) : d197787 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d196021, d197090, d197787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d196021, d197090, d197787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d196022 q = 1) (hb : d197091 q = 1) : d197788 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d196022, d197091, d197788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d196022, d197091, d197788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d196023 q = 1) (hb : d197092 q = 1) : d197789 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d196023, d197092, d197789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d196023, d197092, d197789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d196024 q = 1) (hb : d197093 q = 1) : d197790 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d196024, d197093, d197790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d196024, d197093, d197790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro46966 (p : Pattern) (ha : d196030 p = 1) (hb : d197099 p = 1) : d197796 p = 1 := by
  have h0 (q : Pattern) (ha : d195501 q = 1) (hb : d196264 q = 1) : d197265 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d195501, d196264, d197265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46782 q ha hb
    | true =>
      simp only [d195501, d196264, d197265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46813 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d195620 q = 1) (hb : d196416 q = 1) : d197389 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d195620, d196416, d197389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d195620, d196416, d197389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46846 q ha hb
  have h3 (q : Pattern) (ha : d195621 q = 1) (hb : d196417 q = 1) : d197390 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d195621, d196417, d197390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d195621, d196417, d197390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d195754 q = 1) (hb : d196641 q = 1) : d197522 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d195754, d196641, d197522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d195754, d196641, d197522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46887 q ha hb
  have h5 (q : Pattern) (ha : d195755 q = 1) (hb : d196642 q = 1) : d197523 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d195755, d196642, d197523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d195755, d196642, d197523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d195756 q = 1) (hb : d196643 q = 1) : d197524 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d195756, d196643, d197524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d195756, d196643, d197524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d195889 q = 1) (hb : d196867 q = 1) : d197656 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d195889, d196867, d197656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d195889, d196867, d197656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46927 q ha hb
  have h8 (q : Pattern) (ha : d195890 q = 1) (hb : d196868 q = 1) : d197657 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d195890, d196868, d197657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d195890, d196868, d197657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d195891 q = 1) (hb : d196869 q = 1) : d197658 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d195891, d196869, d197658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d195891, d196869, d197658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d195892 q = 1) (hb : d196870 q = 1) : d197659 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d195892, d196870, d197659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d195892, d196870, d197659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d196025 q = 1) (hb : d197094 q = 1) : d197791 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d196025, d197094, d197791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d196025, d197094, d197791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46965 q ha hb
  have h12 (q : Pattern) (ha : d196026 q = 1) (hb : d197095 q = 1) : d197792 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d196026, d197095, d197792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d196026, d197095, d197792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d196027 q = 1) (hb : d197096 q = 1) : d197793 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d196027, d197096, d197793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d196027, d197096, d197793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d196028 q = 1) (hb : d197097 q = 1) : d197794 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d196028, d197097, d197794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d196028, d197097, d197794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d196029 q = 1) (hb : d197098 q = 1) : d197795 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d196029, d197098, d197795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d196029, d197098, d197795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d196030 q = 1) (hb : d197099 q = 1) : d197796 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d196030, d197099, d197796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d196030, d197099, d197796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro46967 (p : Pattern) (ha : d196036 p = 1) (hb : d197105 p = 1) : d197802 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d196031 q = 1) (hb : d197100 q = 1) : d197797 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d196031, d197100, d197797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46966 q ha hb
    | true =>
      simp only [d196031, d197100, d197797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d196032 q = 1) (hb : d197101 q = 1) : d197798 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d196032, d197101, d197798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d196032, d197101, d197798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d196033 q = 1) (hb : d197102 q = 1) : d197799 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d196033, d197102, d197799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d196033, d197102, d197799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d196034 q = 1) (hb : d197103 q = 1) : d197800 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d196034, d197103, d197800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d196034, d197103, d197800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d196035 q = 1) (hb : d197104 q = 1) : d197801 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d196035, d197104, d197801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d196035, d197104, d197801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d196036 q = 1) (hb : d197105 q = 1) : d197802 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d196036, d197105, d197802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d196036, d197105, d197802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro46968 (p : Pattern) (ha : d196042 p = 1) (hb : d197111 p = 1) : d197808 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d196037 q = 1) (hb : d197106 q = 1) : d197803 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d196037, d197106, d197803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46967 q ha hb
    | true =>
      simp only [d196037, d197106, d197803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d196038 q = 1) (hb : d197107 q = 1) : d197804 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d196038, d197107, d197804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d196038, d197107, d197804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d196039 q = 1) (hb : d197108 q = 1) : d197805 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d196039, d197108, d197805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d196039, d197108, d197805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d196040 q = 1) (hb : d197109 q = 1) : d197806 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d196040, d197109, d197806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d196040, d197109, d197806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d196041 q = 1) (hb : d197110 q = 1) : d197807 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d196041, d197110, d197807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d196041, d197110, d197807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d196042 q = 1) (hb : d197111 q = 1) : d197808 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d196042, d197111, d197808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d196042, d197111, d197808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro46969 (p : Pattern) (ha : d196048 p = 1) (hb : d197117 p = 1) : d197814 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d196043 q = 1) (hb : d197112 q = 1) : d197809 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d196043, d197112, d197809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46968 q ha hb
    | true =>
      simp only [d196043, d197112, d197809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d196044 q = 1) (hb : d197113 q = 1) : d197810 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d196044, d197113, d197810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d196044, d197113, d197810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d196045 q = 1) (hb : d197114 q = 1) : d197811 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d196045, d197114, d197811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d196045, d197114, d197811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d196046 q = 1) (hb : d197115 q = 1) : d197812 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d196046, d197115, d197812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d196046, d197115, d197812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d196047 q = 1) (hb : d197116 q = 1) : d197813 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d196047, d197116, d197813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d196047, d197116, d197813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d196048 q = 1) (hb : d197117 q = 1) : d197814 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d196048, d197117, d197814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d196048, d197117, d197814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro46970 (p : Pattern) (ha : d196054 p = 1) (hb : d197123 p = 1) : d197820 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d196049 q = 1) (hb : d197118 q = 1) : d197815 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d196049, d197118, d197815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46969 q ha hb
    | true =>
      simp only [d196049, d197118, d197815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d196050 q = 1) (hb : d197119 q = 1) : d197816 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d196050, d197119, d197816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d196050, d197119, d197816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d196051 q = 1) (hb : d197120 q = 1) : d197817 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d196051, d197120, d197817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d196051, d197120, d197817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d196052 q = 1) (hb : d197121 q = 1) : d197818 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d196052, d197121, d197818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d196052, d197121, d197818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d196053 q = 1) (hb : d197122 q = 1) : d197819 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d196053, d197122, d197819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d196053, d197122, d197819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d196054 q = 1) (hb : d197123 q = 1) : d197820 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d196054, d197123, d197820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d196054, d197123, d197820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro46971 (p : Pattern) (ha : d196060 p = 1) (hb : d197129 p = 1) : d197826 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d196055 q = 1) (hb : d197124 q = 1) : d197821 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d196055, d197124, d197821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46970 q ha hb
    | true =>
      simp only [d196055, d197124, d197821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d196056 q = 1) (hb : d197125 q = 1) : d197822 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d196056, d197125, d197822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d196056, d197125, d197822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d196057 q = 1) (hb : d197126 q = 1) : d197823 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d196057, d197126, d197823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d196057, d197126, d197823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d196058 q = 1) (hb : d197127 q = 1) : d197824 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d196058, d197127, d197824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d196058, d197127, d197824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d196059 q = 1) (hb : d197128 q = 1) : d197825 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d196059, d197128, d197825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d196059, d197128, d197825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d196060 q = 1) (hb : d197129 q = 1) : d197826 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d196060, d197129, d197826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d196060, d197129, d197826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro46972 (p : Pattern) (ha : d196066 p = 1) (hb : d197135 p = 1) : d197832 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d196061 q = 1) (hb : d197130 q = 1) : d197827 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d196061, d197130, d197827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46971 q ha hb
    | true =>
      simp only [d196061, d197130, d197827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d196062 q = 1) (hb : d197131 q = 1) : d197828 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d196062, d197131, d197828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d196062, d197131, d197828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d196063 q = 1) (hb : d197132 q = 1) : d197829 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d196063, d197132, d197829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d196063, d197132, d197829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d196064 q = 1) (hb : d197133 q = 1) : d197830 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d196064, d197133, d197830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d196064, d197133, d197830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d196065 q = 1) (hb : d197134 q = 1) : d197831 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d196065, d197134, d197831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d196065, d197134, d197831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d196066 q = 1) (hb : d197135 q = 1) : d197832 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d196066, d197135, d197832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d196066, d197135, d197832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro46973 (p : Pattern) (ha : d196072 p = 1) (hb : d197141 p = 1) : d197838 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d196067 q = 1) (hb : d197136 q = 1) : d197833 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d196067, d197136, d197833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46972 q ha hb
    | true =>
      simp only [d196067, d197136, d197833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d196068 q = 1) (hb : d197137 q = 1) : d197834 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d196068, d197137, d197834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d196068, d197137, d197834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d196069 q = 1) (hb : d197138 q = 1) : d197835 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d196069, d197138, d197835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d196069, d197138, d197835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d196070 q = 1) (hb : d197139 q = 1) : d197836 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d196070, d197139, d197836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d196070, d197139, d197836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d196071 q = 1) (hb : d197140 q = 1) : d197837 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d196071, d197140, d197837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d196071, d197140, d197837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d196072 q = 1) (hb : d197141 q = 1) : d197838 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d196072, d197141, d197838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d196072, d197141, d197838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro46974 (p : Pattern) (ha : d116753 p = 1) (hb : d194340 p = 1) : d120334 p = 1 := by
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
  have h2 (q : Pattern) (ha : d20969 q = 1) (hb : d116753 q = 1) : d120139 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20969, d120139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20969, d120139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20970 q = 1) (hb : d116753 q = 1) : d120140 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d20970, d120140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20970, d120140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20971 q = 1) (hb : d116753 q = 1) : d120141 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d20971, d120141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20971, d120141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20972 q = 1) (hb : d116753 q = 1) : d120142 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d20972, d120142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20972, d120142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d116753 q = 1) (hb : d194340 q = 1) : d120334 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d194340, d120334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194340, d120334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro46975 (p : Pattern) (ha : d116753 p = 1) (hb : d194350 p = 1) : d120378 p = 1 := by
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
  have h2 (q : Pattern) (ha : d116753 q = 1) (hb : d194346 q = 1) : d120374 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d194346, d120374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194346, d120374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d116753 q = 1) (hb : d194347 q = 1) : d120375 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d194347, d120375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d194347, d120375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d116753 q = 1) (hb : d194348 q = 1) : d120376 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d194348, d120376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194348, d120376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d116753 q = 1) (hb : d194349 q = 1) : d120377 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d194349, d120377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194349, d120377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d116753 q = 1) (hb : d194350 q = 1) : d120378 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d194350, d120378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194350, d120378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro46976 (p : Pattern) (ha : d116753 p = 1) (hb : d194356 p = 1) : d121355 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20974 q = 1) (hb : d116753 q = 1) : d120144 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d20974, d120144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46472 q ha hb
    | true =>
      simp only [d20974, d120144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46473 q ha hb
  have h2 (q : Pattern) (ha : d20975 q = 1) (hb : d116753 q = 1) : d120145 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d20975, d120145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d20975, d120145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d116753 q = 1) (hb : d194338 q = 1) : d121345 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d194338, d121345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d194338, d121345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d116753 q = 1) (hb : d194339 q = 1) : d121346 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d194339, d121346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194339, d121346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d116753 q = 1) (hb : d194341 q = 1) : d120335 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d194341, d120335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194341, d120335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46974 q ha hb
  have h6 (q : Pattern) (ha : d116753 q = 1) (hb : d194342 q = 1) : d121347 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d194342, d121347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d194342, d121347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d116753 q = 1) (hb : d194343 q = 1) : d121348 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d194343, d121348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d194343, d121348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d116753 q = 1) (hb : d194344 q = 1) : d121349 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d194344, d121349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d194344, d121349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d116753 q = 1) (hb : d194345 q = 1) : d121350 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d194345, d121350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d194345, d121350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d116753 q = 1) (hb : d194351 q = 1) : d120379 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d194351, d120379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194351, d120379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46975 q ha hb
  have h11 (q : Pattern) (ha : d116753 q = 1) (hb : d194352 q = 1) : d121351 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d194352, d121351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d194352, d121351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d116753 q = 1) (hb : d194353 q = 1) : d121352 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d194353, d121352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d194353, d121352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d116753 q = 1) (hb : d194354 q = 1) : d121353 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d194354, d121353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d194354, d121353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d116753 q = 1) (hb : d194355 q = 1) : d121354 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d194355, d121354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d194355, d121354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d116753 q = 1) (hb : d194356 q = 1) : d121355 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d194356, d121355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d194356, d121355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro46977 (p : Pattern) (ha : d116753 p = 1) (hb : d194362 p = 1) : d121361 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53648 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20377 q ha hb
  have h2 (q : Pattern) (ha : d53649 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53650 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53651 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53652 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d116753 q = 1) (hb : d194357 q = 1) : d121356 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d194357, d121356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194357, d121356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46976 q ha hb
  have h7 (q : Pattern) (ha : d116753 q = 1) (hb : d194358 q = 1) : d121357 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d194358, d121357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194358, d121357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d116753 q = 1) (hb : d194359 q = 1) : d121358 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d194359, d121358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194359, d121358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d116753 q = 1) (hb : d194360 q = 1) : d121359 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d194360, d121359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194360, d121359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d116753 q = 1) (hb : d194361 q = 1) : d121360 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d194361, d121360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194361, d121360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d116753 q = 1) (hb : d194362 q = 1) : d121361 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d194362, d121361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d194362, d121361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro46978 (p : Pattern) (ha : d116753 p = 1) (hb : d194365 p = 1) : d197841 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21156 q = 1) (hb : d116753 q = 1) : d196093 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21156, d196093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46500 q ha hb
    | true =>
      simp only [d21156, d196093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46501 q ha hb
  have h2 (q : Pattern) (ha : d21157 q = 1) (hb : d116753 q = 1) : d196149 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21157, d196149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21157, d196149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21158 q = 1) (hb : d116753 q = 1) : d196150 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21158, d196150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21158, d196150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21159 q = 1) (hb : d116753 q = 1) : d196151 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21159, d196151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21159, d196151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21160 q = 1) (hb : d116753 q = 1) : d196152 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d21160, d196152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21160, d196152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d116753 q = 1) (hb : d194365 q = 1) : d197841 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d194365, d197841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194365, d197841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro46979 (p : Pattern) (ha : d116753 p = 1) (hb : d194376 p = 1) : d197851 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d116753 q = 1) (hb : d194371 q = 1) : d196124 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d194371, d196124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46530 q hb ha
    | true =>
      simp only [d194371, d196124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46507 q hb ha
  have h2 (q : Pattern) (ha : d116753 q = 1) (hb : d194372 q = 1) : d197847 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d194372, d197847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194372, d197847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d116753 q = 1) (hb : d194373 q = 1) : d197848 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d194373, d197848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d194373, d197848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d116753 q = 1) (hb : d194374 q = 1) : d197849 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d194374, d197849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194374, d197849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d116753 q = 1) (hb : d194375 q = 1) : d197850 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d194375, d197850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194375, d197850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d116753 q = 1) (hb : d194376 q = 1) : d197851 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d194376, d197851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194376, d197851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro46980 (p : Pattern) (ha : d116753 p = 1) (hb : d194382 p = 1) : d197857 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21162 q = 1) (hb : d116753 q = 1) : d196154 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d21162, d196154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46499 q ha hb
    | true =>
      simp only [d21162, d196154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46502 q ha hb
  have h2 (q : Pattern) (ha : d21163 q = 1) (hb : d116753 q = 1) : d196155 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d21163, d196155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d21163, d196155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d116753 q = 1) (hb : d194363 q = 1) : d197839 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d194363, d197839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d194363, d197839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d116753 q = 1) (hb : d194364 q = 1) : d197840 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d194364, d197840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194364, d197840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d116753 q = 1) (hb : d194366 q = 1) : d197842 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d194366, d197842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194366, d197842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46978 q ha hb
  have h6 (q : Pattern) (ha : d116753 q = 1) (hb : d194367 q = 1) : d197843 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d194367, d197843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d194367, d197843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d116753 q = 1) (hb : d194368 q = 1) : d197844 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d194368, d197844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d194368, d197844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d116753 q = 1) (hb : d194369 q = 1) : d197845 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d194369, d197845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d194369, d197845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d116753 q = 1) (hb : d194370 q = 1) : d197846 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d194370, d197846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d194370, d197846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d116753 q = 1) (hb : d194377 q = 1) : d197852 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d194377, d197852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194377, d197852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46979 q ha hb
  have h11 (q : Pattern) (ha : d116753 q = 1) (hb : d194378 q = 1) : d197853 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d194378, d197853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d194378, d197853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d116753 q = 1) (hb : d194379 q = 1) : d197854 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d194379, d197854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d194379, d197854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d116753 q = 1) (hb : d194380 q = 1) : d197855 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d194380, d197855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d194380, d197855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d116753 q = 1) (hb : d194381 q = 1) : d197856 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d194381, d197856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d194381, d197856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d116753 q = 1) (hb : d194382 q = 1) : d197857 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d194382, d197857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d194382, d197857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro46981 (p : Pattern) (ha : d116753 p = 1) (hb : d194388 p = 1) : d197863 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d116753 q = 1) (hb : d194383 q = 1) : d197858 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d194383, d197858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194383, d197858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46980 q ha hb
  have h2 (q : Pattern) (ha : d116753 q = 1) (hb : d194384 q = 1) : d197859 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d194384, d197859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194384, d197859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d116753 q = 1) (hb : d194385 q = 1) : d197860 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d194385, d197860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194385, d197860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d116753 q = 1) (hb : d194386 q = 1) : d197861 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d194386, d197861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194386, d197861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d116753 q = 1) (hb : d194387 q = 1) : d197862 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d194387, d197862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194387, d197862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d116753 q = 1) (hb : d194388 q = 1) : d197863 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d194388, d197863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194388, d197863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro46982 (p : Pattern) (ha : d116753 p = 1) (hb : d194392 p = 1) : d197867 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21455 q = 1) (hb : d116753 q = 1) : d196287 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21455, d196287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46542 q ha hb
    | true =>
      simp only [d21455, d196287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46543 q ha hb
  have h2 (q : Pattern) (ha : d21456 q = 1) (hb : d116753 q = 1) : d196288 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21456, d196288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21456, d196288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21457 q = 1) (hb : d116753 q = 1) : d196289 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21457, d196289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21457, d196289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21458 q = 1) (hb : d116753 q = 1) : d196290 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21458, d196290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21458, d196290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21459 q = 1) (hb : d116753 q = 1) : d196291 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d21459, d196291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21459, d196291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d116753 q = 1) (hb : d194392 q = 1) : d197867 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d194392, d197867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194392, d197867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro46983 (p : Pattern) (ha : d116753 p = 1) (hb : d194403 p = 1) : d197878 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d116753 q = 1) (hb : d194398 q = 1) : d197873 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d194398, d197873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46574 q hb ha
    | true =>
      simp only [d194398, d197873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46550 q hb ha
  have h2 (q : Pattern) (ha : d116753 q = 1) (hb : d194399 q = 1) : d197874 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d194399, d197874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194399, d197874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d116753 q = 1) (hb : d194400 q = 1) : d197875 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d194400, d197875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d194400, d197875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d116753 q = 1) (hb : d194401 q = 1) : d197876 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d194401, d197876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194401, d197876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d116753 q = 1) (hb : d194402 q = 1) : d197877 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d194402, d197877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194402, d197877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d116753 q = 1) (hb : d194403 q = 1) : d197878 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d194403, d197878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194403, d197878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro46984 (p : Pattern) (ha : d116753 p = 1) (hb : d194409 p = 1) : d197884 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21461 q = 1) (hb : d116753 q = 1) : d196293 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d21461, d196293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46541 q ha hb
    | true =>
      simp only [d21461, d196293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46544 q ha hb
  have h2 (q : Pattern) (ha : d21462 q = 1) (hb : d116753 q = 1) : d196294 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d21462, d196294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d21462, d196294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d116753 q = 1) (hb : d194390 q = 1) : d197865 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d194390, d197865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d194390, d197865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d116753 q = 1) (hb : d194391 q = 1) : d197866 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d194391, d197866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194391, d197866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d116753 q = 1) (hb : d194393 q = 1) : d197868 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d194393, d197868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194393, d197868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46982 q ha hb
  have h6 (q : Pattern) (ha : d116753 q = 1) (hb : d194394 q = 1) : d197869 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d194394, d197869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d194394, d197869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d116753 q = 1) (hb : d194395 q = 1) : d197870 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d194395, d197870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d194395, d197870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d116753 q = 1) (hb : d194396 q = 1) : d197871 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d194396, d197871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d194396, d197871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d116753 q = 1) (hb : d194397 q = 1) : d197872 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d194397, d197872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d194397, d197872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d116753 q = 1) (hb : d194404 q = 1) : d197879 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d194404, d197879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194404, d197879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46983 q ha hb
  have h11 (q : Pattern) (ha : d116753 q = 1) (hb : d194405 q = 1) : d197880 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d194405, d197880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d194405, d197880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d116753 q = 1) (hb : d194406 q = 1) : d197881 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d194406, d197881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d194406, d197881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d116753 q = 1) (hb : d194407 q = 1) : d197882 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d194407, d197882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d194407, d197882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d116753 q = 1) (hb : d194408 q = 1) : d197883 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d194408, d197883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d194408, d197883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d116753 q = 1) (hb : d194409 q = 1) : d197884 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d194409, d197884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d194409, d197884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro46985 (p : Pattern) (ha : d116753 p = 1) (hb : d194415 p = 1) : d197890 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d116753 q = 1) (hb : d194410 q = 1) : d197885 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d194410, d197885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194410, d197885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46984 q ha hb
  have h2 (q : Pattern) (ha : d116753 q = 1) (hb : d194411 q = 1) : d197886 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d194411, d197886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194411, d197886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d116753 q = 1) (hb : d194412 q = 1) : d197887 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d194412, d197887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194412, d197887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d116753 q = 1) (hb : d194413 q = 1) : d197888 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d194413, d197888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194413, d197888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d116753 q = 1) (hb : d194414 q = 1) : d197889 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d194414, d197889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194414, d197889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d116753 q = 1) (hb : d194415 q = 1) : d197890 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d194415, d197890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194415, d197890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro46986 (p : Pattern) (ha : d116753 p = 1) (hb : d194420 p = 1) : d197895 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21808 q = 1) (hb : d116753 q = 1) : d196455 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21808, d196455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46587 q ha hb
    | true =>
      simp only [d21808, d196455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46588 q ha hb
  have h2 (q : Pattern) (ha : d21809 q = 1) (hb : d116753 q = 1) : d196456 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21809, d196456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21809, d196456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21810 q = 1) (hb : d116753 q = 1) : d196457 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21810, d196457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21810, d196457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21811 q = 1) (hb : d116753 q = 1) : d196458 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21811, d196458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21811, d196458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21812 q = 1) (hb : d116753 q = 1) : d196459 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d21812, d196459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21812, d196459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d116753 q = 1) (hb : d194420 q = 1) : d197895 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d194420, d197895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194420, d197895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro46987 (p : Pattern) (ha : d116753 p = 1) (hb : d194427 p = 1) : d196583 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116752 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22070 q = 1) (hb : d116752 q = 1) : d196569 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22070, d196569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46622 q ha hb
    | true =>
      simp only [d22070, d196569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46596 q ha hb
  have h2 (q : Pattern) (ha : d22071 q = 1) (hb : d116752 q = 1) : d196570 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22071, d196570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22071, d196570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22072 q = 1) (hb : d116752 q = 1) : d196571 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22072, d196571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22072, d196571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d22081 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d22082 q = 1) (hb : d116753 q = 1) : d196572 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22082, d116753, d196572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22082, d116753, d196572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d22098 q = 1) (hb : d116752 q = 1) : d196578 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22098, d196578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46596 q ha hb
    | true =>
      simp only [d22098, d196578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46597 q ha hb
  have h7 (q : Pattern) (ha : d22099 q = 1) (hb : d116752 q = 1) : d196579 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22099, d196579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22099, d196579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d22100 q = 1) (hb : d116752 q = 1) : d196580 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22100, d196580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22100, d196580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d22101 q = 1) (hb : d116753 q = 1) : d196581 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22101, d116753, d196581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d22101, d116753, d196581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d116753 q = 1) (hb : d194426 q = 1) : d196582 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d194426, d196582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d194426, d196582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d116753 q = 1) (hb : d194427 q = 1) : d196583 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d194427, d196583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d194427, d196583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  exact h13 p ha hb
theorem andIntro46988 (p : Pattern) (ha : d116753 p = 1) (hb : d194433 p = 1) : d196597 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d116753 q = 1) (hb : d194428 q = 1) : d196584 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d194428, d196584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46987 q ha hb
    | true =>
      simp only [d194428, d196584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d116753 q = 1) (hb : d194429 q = 1) : d196585 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d194429, d196585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194429, d196585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22104 q = 1) (hb : d116753 q = 1) : d196592 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22104, d196592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46598 q ha hb
    | true =>
      simp only [d22104, d196592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22105 q = 1) (hb : d116753 q = 1) : d196593 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22105, d196593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22105, d196593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d116753 q = 1) (hb : d194430 q = 1) : d196594 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d194430, d196594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d194430, d196594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d116753 q = 1) (hb : d194431 q = 1) : d196595 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d194431, d196595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d194431, d196595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d116753 q = 1) (hb : d194432 q = 1) : d196596 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d194432, d196596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d194432, d196596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d116753 q = 1) (hb : d194433 q = 1) : d196597 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d194433, d196597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d194433, d196597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro46989 (p : Pattern) (ha : d116753 p = 1) (hb : d194439 p = 1) : d197906 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d116753 q = 1) (hb : d194434 q = 1) : d197901 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d194434, d197901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46988 q ha hb
    | true =>
      simp only [d194434, d197901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46599 q hb ha
  have h2 (q : Pattern) (ha : d116753 q = 1) (hb : d194435 q = 1) : d197902 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d194435, d197902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194435, d197902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d116753 q = 1) (hb : d194436 q = 1) : d197903 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d194436, d197903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d194436, d197903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d116753 q = 1) (hb : d194437 q = 1) : d197904 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d194437, d197904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194437, d197904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d116753 q = 1) (hb : d194438 q = 1) : d197905 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d194438, d197905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194438, d197905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d116753 q = 1) (hb : d194439 q = 1) : d197906 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d194439, d197906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194439, d197906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro46990 (p : Pattern) (ha : d116753 p = 1) (hb : d194445 p = 1) : d197912 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21814 q = 1) (hb : d116753 q = 1) : d196461 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d21814, d196461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46586 q ha hb
    | true =>
      simp only [d21814, d196461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46589 q ha hb
  have h2 (q : Pattern) (ha : d21815 q = 1) (hb : d116753 q = 1) : d196462 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d21815, d196462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d21815, d196462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d116753 q = 1) (hb : d194418 q = 1) : d197893 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d194418, d197893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d194418, d197893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d116753 q = 1) (hb : d194419 q = 1) : d197894 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d194419, d197894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194419, d197894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d116753 q = 1) (hb : d194421 q = 1) : d197896 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d194421, d197896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194421, d197896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46986 q ha hb
  have h6 (q : Pattern) (ha : d116753 q = 1) (hb : d194422 q = 1) : d197897 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d194422, d197897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d194422, d197897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d116753 q = 1) (hb : d194423 q = 1) : d197898 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d194423, d197898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d194423, d197898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d116753 q = 1) (hb : d194424 q = 1) : d197899 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d194424, d197899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d194424, d197899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d116753 q = 1) (hb : d194425 q = 1) : d197900 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d194425, d197900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d194425, d197900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d116753 q = 1) (hb : d194440 q = 1) : d197907 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d194440, d197907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194440, d197907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46989 q ha hb
  have h11 (q : Pattern) (ha : d116753 q = 1) (hb : d194441 q = 1) : d197908 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d194441, d197908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d194441, d197908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d116753 q = 1) (hb : d194442 q = 1) : d197909 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d194442, d197909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d194442, d197909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d116753 q = 1) (hb : d194443 q = 1) : d197910 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d194443, d197910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d194443, d197910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d116753 q = 1) (hb : d194444 q = 1) : d197911 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d194444, d197911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d194444, d197911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d116753 q = 1) (hb : d194445 q = 1) : d197912 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d194445, d197912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d194445, d197912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro46991 (p : Pattern) (ha : d116753 p = 1) (hb : d194451 p = 1) : d197918 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d116753 q = 1) (hb : d194446 q = 1) : d197913 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d194446, d197913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194446, d197913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46990 q ha hb
  have h2 (q : Pattern) (ha : d116753 q = 1) (hb : d194447 q = 1) : d197914 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d194447, d197914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194447, d197914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d116753 q = 1) (hb : d194448 q = 1) : d197915 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d194448, d197915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194448, d197915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d116753 q = 1) (hb : d194449 q = 1) : d197916 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d194449, d197916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194449, d197916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d116753 q = 1) (hb : d194450 q = 1) : d197917 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d194450, d197917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194450, d197917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d116753 q = 1) (hb : d194451 q = 1) : d197918 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d194451, d197918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194451, d197918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro46992 (p : Pattern) (ha : d116753 p = 1) (hb : d194457 p = 1) : d197924 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22286 q = 1) (hb : d116753 q = 1) : d196681 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22286, d196681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46642 q ha hb
    | true =>
      simp only [d22286, d196681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46643 q ha hb
  have h2 (q : Pattern) (ha : d22287 q = 1) (hb : d116753 q = 1) : d196682 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22287, d196682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22287, d196682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22288 q = 1) (hb : d116753 q = 1) : d196683 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22288, d196683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22288, d196683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22289 q = 1) (hb : d116753 q = 1) : d196684 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d22289, d196684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22289, d196684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22290 q = 1) (hb : d116753 q = 1) : d196685 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d22290, d196685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22290, d196685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d116753 q = 1) (hb : d194457 q = 1) : d197924 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d194457, d197924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194457, d197924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro46993 (p : Pattern) (ha : d116753 p = 1) (hb : d194464 p = 1) : d196809 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116752 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22535 q = 1) (hb : d116752 q = 1) : d196795 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22535, d196795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46677 q ha hb
    | true =>
      simp only [d22535, d196795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46651 q ha hb
  have h2 (q : Pattern) (ha : d22536 q = 1) (hb : d116752 q = 1) : d196796 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22536, d196796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22536, d196796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22537 q = 1) (hb : d116752 q = 1) : d196797 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22537, d196797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22537, d196797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d22546 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d22547 q = 1) (hb : d116753 q = 1) : d196798 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22547, d116753, d196798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22547, d116753, d196798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d22563 q = 1) (hb : d116752 q = 1) : d196804 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22563, d196804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46651 q ha hb
    | true =>
      simp only [d22563, d196804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46652 q ha hb
  have h7 (q : Pattern) (ha : d22564 q = 1) (hb : d116752 q = 1) : d196805 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22564, d196805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22564, d196805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d22565 q = 1) (hb : d116752 q = 1) : d196806 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22565, d196806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22565, d196806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d22566 q = 1) (hb : d116753 q = 1) : d196807 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22566, d116753, d196807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d22566, d116753, d196807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d116753 q = 1) (hb : d194463 q = 1) : d196808 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d194463, d196808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d194463, d196808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d116753 q = 1) (hb : d194464 q = 1) : d196809 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d194464, d196809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d194464, d196809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  exact h13 p ha hb
theorem andIntro46994 (p : Pattern) (ha : d116753 p = 1) (hb : d194470 p = 1) : d196823 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d116753 q = 1) (hb : d194465 q = 1) : d196810 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d194465, d196810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46993 q ha hb
    | true =>
      simp only [d194465, d196810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d116753 q = 1) (hb : d194466 q = 1) : d196811 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d194466, d196811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194466, d196811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22569 q = 1) (hb : d116753 q = 1) : d196818 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22569, d196818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46653 q ha hb
    | true =>
      simp only [d22569, d196818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22570 q = 1) (hb : d116753 q = 1) : d196819 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22570, d196819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22570, d196819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d116753 q = 1) (hb : d194467 q = 1) : d196820 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d194467, d196820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d194467, d196820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d116753 q = 1) (hb : d194468 q = 1) : d196821 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d194468, d196821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d194468, d196821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d116753 q = 1) (hb : d194469 q = 1) : d196822 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d194469, d196822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d194469, d196822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d116753 q = 1) (hb : d194470 q = 1) : d196823 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d194470, d196823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d194470, d196823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro46995 (p : Pattern) (ha : d116753 p = 1) (hb : d194476 p = 1) : d197935 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d116753 q = 1) (hb : d194471 q = 1) : d197930 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d194471, d197930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46994 q ha hb
    | true =>
      simp only [d194471, d197930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46654 q hb ha
  have h2 (q : Pattern) (ha : d116753 q = 1) (hb : d194472 q = 1) : d197931 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d194472, d197931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194472, d197931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d116753 q = 1) (hb : d194473 q = 1) : d197932 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d194473, d197932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d194473, d197932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d116753 q = 1) (hb : d194474 q = 1) : d197933 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d194474, d197933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194474, d197933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d116753 q = 1) (hb : d194475 q = 1) : d197934 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d194475, d197934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194475, d197934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d116753 q = 1) (hb : d194476 q = 1) : d197935 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d194476, d197935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194476, d197935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro46996 (p : Pattern) (ha : d116753 p = 1) (hb : d194482 p = 1) : d197941 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22292 q = 1) (hb : d116753 q = 1) : d196687 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d22292, d196687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46641 q ha hb
    | true =>
      simp only [d22292, d196687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46644 q ha hb
  have h2 (q : Pattern) (ha : d22293 q = 1) (hb : d116753 q = 1) : d196688 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d22293, d196688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d22293, d196688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d116753 q = 1) (hb : d194455 q = 1) : d197922 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d194455, d197922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d194455, d197922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d116753 q = 1) (hb : d194456 q = 1) : d197923 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d194456, d197923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194456, d197923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d116753 q = 1) (hb : d194458 q = 1) : d197925 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d194458, d197925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194458, d197925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46992 q ha hb
  have h6 (q : Pattern) (ha : d116753 q = 1) (hb : d194459 q = 1) : d197926 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d194459, d197926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d194459, d197926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d116753 q = 1) (hb : d194460 q = 1) : d197927 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d194460, d197927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d194460, d197927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d116753 q = 1) (hb : d194461 q = 1) : d197928 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d194461, d197928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d194461, d197928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d116753 q = 1) (hb : d194462 q = 1) : d197929 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d194462, d197929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d194462, d197929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d116753 q = 1) (hb : d194477 q = 1) : d197936 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d194477, d197936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194477, d197936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46995 q ha hb
  have h11 (q : Pattern) (ha : d116753 q = 1) (hb : d194478 q = 1) : d197937 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d194478, d197937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d194478, d197937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d116753 q = 1) (hb : d194479 q = 1) : d197938 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d194479, d197938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d194479, d197938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d116753 q = 1) (hb : d194480 q = 1) : d197939 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d194480, d197939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d194480, d197939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d116753 q = 1) (hb : d194481 q = 1) : d197940 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d194481, d197940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d194481, d197940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d116753 q = 1) (hb : d194482 q = 1) : d197941 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d194482, d197941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d194482, d197941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro46997 (p : Pattern) (ha : d116753 p = 1) (hb : d194488 p = 1) : d197947 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d116753 q = 1) (hb : d194483 q = 1) : d197942 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d194483, d197942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194483, d197942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46996 q ha hb
  have h2 (q : Pattern) (ha : d116753 q = 1) (hb : d194484 q = 1) : d197943 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d194484, d197943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194484, d197943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d116753 q = 1) (hb : d194485 q = 1) : d197944 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d194485, d197944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194485, d197944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d116753 q = 1) (hb : d194486 q = 1) : d197945 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d194486, d197945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194486, d197945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d116753 q = 1) (hb : d194487 q = 1) : d197946 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d194487, d197946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194487, d197946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d116753 q = 1) (hb : d194488 q = 1) : d197947 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d194488, d197947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194488, d197947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro46998 (p : Pattern) (ha : d116753 p = 1) (hb : d194495 p = 1) : d197954 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22741 q = 1) (hb : d116753 q = 1) : d196908 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22741, d196908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46697 q ha hb
    | true =>
      simp only [d22741, d196908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46698 q ha hb
  have h2 (q : Pattern) (ha : d22742 q = 1) (hb : d116753 q = 1) : d196909 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22742, d196909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22742, d196909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22743 q = 1) (hb : d116753 q = 1) : d196910 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22743, d196910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22743, d196910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22744 q = 1) (hb : d116753 q = 1) : d196911 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d22744, d196911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22744, d196911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22745 q = 1) (hb : d116753 q = 1) : d196912 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d22745, d196912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22745, d196912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d116753 q = 1) (hb : d194495 q = 1) : d197954 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d194495, d197954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194495, d197954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro46999 (p : Pattern) (ha : d116753 p = 1) (hb : d194502 p = 1) : d197036 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116752 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22949 q = 1) (hb : d116752 q = 1) : d197022 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22949, d197022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46732 q ha hb
    | true =>
      simp only [d22949, d197022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46706 q ha hb
  have h2 (q : Pattern) (ha : d22950 q = 1) (hb : d116752 q = 1) : d197023 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22950, d197023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22950, d197023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22951 q = 1) (hb : d116752 q = 1) : d197024 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22951, d197024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22951, d197024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d22960 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d22961 q = 1) (hb : d116753 q = 1) : d197025 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22961, d116753, d197025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22961, d116753, d197025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d22977 q = 1) (hb : d116752 q = 1) : d197031 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22977, d197031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46706 q ha hb
    | true =>
      simp only [d22977, d197031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46707 q ha hb
  have h7 (q : Pattern) (ha : d22978 q = 1) (hb : d116752 q = 1) : d197032 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22978, d197032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22978, d197032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d22979 q = 1) (hb : d116752 q = 1) : d197033 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22979, d197033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22979, d197033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d22980 q = 1) (hb : d116753 q = 1) : d197034 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22980, d116753, d197034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d22980, d116753, d197034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d116753 q = 1) (hb : d194501 q = 1) : d197035 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d194501, d197035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d194501, d197035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d116753 q = 1) (hb : d194502 q = 1) : d197036 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d194502, d197036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d194502, d197036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  exact h13 p ha hb
end NetHack.Soko22Hazard87
