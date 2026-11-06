import NetHack.Soko22Hazard87.AndIntroBlocks0386
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro96750 (p : Pattern) (ha : d354331 p = 1) (hb : d355969 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d354326 q = 1) (hb : d355964 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d354326, d355964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96749 q ha hb
    | true =>
      simp only [d354326, d355964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96728 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d354201 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d354327 q = 1) (hb : d355965 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d354327, d355965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d354327, d355965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d354201 q = 1) (hb : d355840 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d354201, d355840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96728 q ha hb
    | true =>
      simp only [d354201, d355840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d354202 q = 1) (hb : d355841 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d354202, d355841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d354202, d355841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d354328 q = 1) (hb : d355966 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d354328, d355966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d354328, d355966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d354329 q = 1) (hb : d355967 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d354329, d355967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354329, d355967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d354330 q = 1) (hb : d355968 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d354330, d355968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354330, d355968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d354331 q = 1) (hb : d355969 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d354331, d355969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354331, d355969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro96751 (p : Pattern) (ha : d354337 p = 1) (hb : d355975 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d354223 q = 1) (hb : d355862 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d354223, d355862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354223, d355862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96731 q ha hb
  have h2 (q : Pattern) (ha : d354224 q = 1) (hb : d355863 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d354224, d355863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d354224, d355863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d354230 q = 1) (hb : d355869 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d354230, d355869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96731 q ha hb
    | true =>
      simp only [d354230, d355869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96732 q ha hb
  have h4 (q : Pattern) (ha : d354231 q = 1) (hb : d355870 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d354231, d355870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d354231, d355870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d354232 q = 1) (hb : d355871 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d354232, d355871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d354232, d355871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d354294 q = 1) (hb : d355932 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d354294, d355932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96740 q ha hb
    | true =>
      simp only [d354294, d355932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96744 q ha hb
  have h7 (q : Pattern) (ha : d354296 q = 1) (hb : d355934 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d354296, d355934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96745 q ha hb
    | true =>
      simp only [d354296, d355934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d354297 q = 1) (hb : d355935 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d354297, d355935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d354297, d355935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d354298 q = 1) (hb : d355936 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d354298, d355936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d354298, d355936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d354299 q = 1) (hb : d355937 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d354299, d355937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d354299, d355937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d354303 q = 1) (hb : d355941 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d354303, d355941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354303, d355941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96746 q ha hb
  have h12 (q : Pattern) (ha : d354304 q = 1) (hb : d355942 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d354304, d355942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d354304, d355942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d354305 q = 1) (hb : d355943 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d354305, d355943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d354305, d355943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d354306 q = 1) (hb : d355944 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d354306, d355944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d354306, d355944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d354307 q = 1) (hb : d355945 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d354307, d355945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d354307, d355945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d354332 q = 1) (hb : d355970 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d354332, d355970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354332, d355970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96750 q ha hb
  have h17 (q : Pattern) (ha : d354333 q = 1) (hb : d355971 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d354333, d355971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d354333, d355971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d354334 q = 1) (hb : d355972 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d354334, d355972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d354334, d355972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d354335 q = 1) (hb : d355973 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d354335, d355973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d354335, d355973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d354336 q = 1) (hb : d355974 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d354336, d355974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d354336, d355974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d354337 q = 1) (hb : d355975 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d354337, d355975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d354337, d355975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro96752 (p : Pattern) (ha : d354343 p = 1) (hb : d355981 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d354213 q = 1) (hb : d355852 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d354213, d355852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354213, d355852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96730 q ha hb
  have h2 (q : Pattern) (ha : d354214 q = 1) (hb : d355853 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d354214, d355853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354214, d355853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d354215 q = 1) (hb : d355854 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d354215, d355854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354215, d355854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d354216 q = 1) (hb : d355855 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d354216, d355855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354216, d355855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d354217 q = 1) (hb : d355856 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d354217, d355856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354217, d355856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d354338 q = 1) (hb : d355976 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d354338, d355976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354338, d355976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96751 q ha hb
  have h7 (q : Pattern) (ha : d354339 q = 1) (hb : d355977 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d354339, d355977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354339, d355977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d354340 q = 1) (hb : d355978 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d354340, d355978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354340, d355978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d354341 q = 1) (hb : d355979 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d354341, d355979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354341, d355979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d354342 q = 1) (hb : d355980 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d354342, d355980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354342, d355980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d354343 q = 1) (hb : d355981 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d354343, d355981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d354343, d355981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro96753 (p : Pattern) (ha : d354348 p = 1) (hb : d355986 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d354272 q = 1) (hb : d355910 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d354272, d355910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96739 q ha hb
    | true =>
      simp only [d354272, d355910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96721 q ha hb
  have h2 (q : Pattern) (ha : d354344 q = 1) (hb : d355982 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d354344, d355982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354344, d355982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d354345 q = 1) (hb : d355983 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d354345, d355983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d354345, d355983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d354346 q = 1) (hb : d355984 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d354346, d355984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354346, d355984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d354347 q = 1) (hb : d355985 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d354347, d355985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354347, d355985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d354348 q = 1) (hb : d355986 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d354348, d355986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354348, d355986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro96754 (p : Pattern) (ha : d354355 p = 1) (hb : d355993 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d354272 q = 1) (hb : d355910 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d354272, d355910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96739 q ha hb
    | true =>
      simp only [d354272, d355910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96721 q ha hb
  have h2 (q : Pattern) (ha : d354344 q = 1) (hb : d355982 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d354344, d355982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354344, d355982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d354345 q = 1) (hb : d355983 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d354345, d355983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d354345, d355983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d354346 q = 1) (hb : d355984 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d354346, d355984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354346, d355984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d354347 q = 1) (hb : d355985 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d354347, d355985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354347, d355985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d354288 q = 1) (hb : d355926 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d354288, d355926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96743 q ha hb
    | true =>
      simp only [d354288, d355926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96723 q ha hb
  have h7 (q : Pattern) (ha : d354351 q = 1) (hb : d355989 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d354351, d355989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354351, d355989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d354352 q = 1) (hb : d355990 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d354352, d355990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d354352, d355990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d354353 q = 1) (hb : d355991 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d354353, d355991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354353, d355991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d354354 q = 1) (hb : d355992 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d354354, d355992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354354, d355992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d354355 q = 1) (hb : d355993 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d354355, d355993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d354355, d355993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro96755 (p : Pattern) (ha : d354360 p = 1) (hb : d355998 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d354266 q = 1) (hb : d355904 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d354266, d355904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96738 q ha hb
    | true =>
      simp only [d354266, d355904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d354267 q = 1) (hb : d355905 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d354267, d355905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354267, d355905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d354154 q = 1) (hb : d355793 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d354154, d355793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96720 q ha hb
    | true =>
      simp only [d354154, d355793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d354155 q = 1) (hb : d355794 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d354155, d355794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354155, d355794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d354268 q = 1) (hb : d355906 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d354268, d355906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d354268, d355906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d354269 q = 1) (hb : d355907 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d354269, d355907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d354269, d355907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d354359 q = 1) (hb : d355997 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d354359, d355997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354359, d355997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d354360 q = 1) (hb : d355998 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d354360, d355998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354360, d355998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro96756 (p : Pattern) (ha : d354367 p = 1) (hb : d356005 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d354266 q = 1) (hb : d355904 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d354266, d355904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96738 q ha hb
    | true =>
      simp only [d354266, d355904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d354267 q = 1) (hb : d355905 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d354267, d355905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354267, d355905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d354154 q = 1) (hb : d355793 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d354154, d355793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96720 q ha hb
    | true =>
      simp only [d354154, d355793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d354155 q = 1) (hb : d355794 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d354155, d355794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354155, d355794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d354268 q = 1) (hb : d355906 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d354268, d355906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d354268, d355906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d354365 q = 1) (hb : d356003 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d354365, d356003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354365, d356003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d354366 q = 1) (hb : d356004 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d354366, d356004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d354366, d356004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d354367 q = 1) (hb : d356005 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d354367, d356005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354367, d356005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro96757 (p : Pattern) (ha : d354247 p = 1) (hb : d356014 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d253269 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d44880 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d46864 q = 1) (hb : d253268 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d46864, d253268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d46864, d253268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d276820 q = 1) (hb : d354245 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d276820, d354245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d276820, d354245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d46865 q = 1) (hb : d354133 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d46865, d354133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46865, d354133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h6 (q : Pattern) (ha : d354246 q = 1) (hb : d355884 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d354246, d355884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d354246, d355884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d354134 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d354247 q = 1) (hb : d356014 q = 1) : d0 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d354247, d356014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d354247, d356014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro96758 (p : Pattern) (ha : d354374 p = 1) (hb : d356010 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d354371 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d44880 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d46864 q = 1) (hb : d253268 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d46864, d253268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d46864, d253268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d276820 q = 1) (hb : d354372 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d276820, d354372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d276820, d354372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d354373 q = 1) (hb : d356009 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d354373, d356009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354373, d356009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d253269 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d276820 q = 1) (hb : d354245 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d276820, d354245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d276820, d354245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h8 (q : Pattern) (ha : d46865 q = 1) (hb : d354133 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d46865, d354133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46865, d354133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h9 (q : Pattern) (ha : d354246 q = 1) (hb : d355884 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d354246, d355884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d354246, d355884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d354374 q = 1) (hb : d356010 q = 1) : d0 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d354374, d356010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d354374, d356010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro96759 (p : Pattern) (ha : d354380 p = 1) (hb : d356020 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d354375 q = 1) (hb : d356011 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d354375, d356011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96758 q ha hb
    | true =>
      simp only [d354375, d356011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d354376 q = 1) (hb : d356012 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d354376, d356012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d354376, d356012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d354248 q = 1) (hb : d355886 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d354248, d355886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96735 q ha hb
    | true =>
      simp only [d354248, d355886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d354249 q = 1) (hb : d355887 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d354249, d355887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d354249, d355887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d354377 q = 1) (hb : d356013 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d354377, d356013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d354377, d356013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d354248 q = 1) (hb : d356015 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d354248, d356015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96757 q ha hb
    | true =>
      simp only [d354248, d356015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d354249 q = 1) (hb : d356016 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d354249, d356016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d354249, d356016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d46871 q = 1) (hb : d354136 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d46871, d354136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96717 q ha hb
    | true =>
      simp only [d46871, d354136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d354137 q = 1) (hb : d355776 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d354137, d355776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d354137, d355776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d354250 q = 1) (hb : d356017 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d354250, d356017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d354250, d356017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d354378 q = 1) (hb : d356018 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d354378, d356018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d354378, d356018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d354379 q = 1) (hb : d356019 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d354379, d356019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d354379, d356019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d354250 q = 1) (hb : d355888 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d354250, d355888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d354250, d355888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h14 (q : Pattern) (ha : d354138 q = 1) (hb : d355777 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d354138, d355777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d354138, d355777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d354251 q = 1) (hb : d355889 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d354251, d355889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d354251, d355889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d354252 q = 1) (hb : d355890 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d354252, d355890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d354252, d355890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h17 (q : Pattern) (ha : d354380 q = 1) (hb : d356020 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d354380, d356020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d354380, d356020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro96760 (p : Pattern) (ha : d354388 p = 1) (hb : d356028 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d354248 q = 1) (hb : d355886 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d354248, d355886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96735 q ha hb
    | true =>
      simp only [d354248, d355886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d354249 q = 1) (hb : d355887 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d354249, d355887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d354249, d355887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d46871 q = 1) (hb : d354136 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d46871, d354136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96717 q ha hb
    | true =>
      simp only [d46871, d354136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d354137 q = 1) (hb : d355776 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d354137, d355776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d354137, d355776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d354250 q = 1) (hb : d355888 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d354250, d355888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d354250, d355888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d354386 q = 1) (hb : d356026 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d354386, d356026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d354386, d356026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d354387 q = 1) (hb : d356027 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d354387, d356027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d354387, d356027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d354138 q = 1) (hb : d355777 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d354138, d355777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d354138, d355777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d354139 q = 1) (hb : d355778 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d354139, d355778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d354139, d355778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d354140 q = 1) (hb : d355779 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d354140, d355779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d354140, d355779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d354388 q = 1) (hb : d356028 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d354388, d356028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d354388, d356028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro96761 (p : Pattern) (ha : d354394 p = 1) (hb : d356034 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d354381 q = 1) (hb : d356021 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d354381, d356021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96759 q ha hb
    | true =>
      simp only [d354381, d356021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d354382 q = 1) (hb : d356022 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d354382, d356022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d354382, d356022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d354383 q = 1) (hb : d356023 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d354383, d356023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354383, d356023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d354384 q = 1) (hb : d356024 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d354384, d356024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d354384, d356024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d354254 q = 1) (hb : d355892 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d354254, d355892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96736 q ha hb
    | true =>
      simp only [d354254, d355892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d354255 q = 1) (hb : d355893 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d354255, d355893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d354255, d355893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d354256 q = 1) (hb : d355894 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d354256, d355894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354256, d355894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d354257 q = 1) (hb : d355895 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d354257, d355895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d354257, d355895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d354385 q = 1) (hb : d356025 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d354385, d356025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d354385, d356025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d354389 q = 1) (hb : d356029 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d354389, d356029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96760 q ha hb
    | true =>
      simp only [d354389, d356029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d354390 q = 1) (hb : d356030 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d354390, d356030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d354390, d356030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d354391 q = 1) (hb : d356031 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d354391, d356031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354391, d356031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d354392 q = 1) (hb : d356032 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d354392, d356032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d354392, d356032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d354142 q = 1) (hb : d355781 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d354142, d355781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96718 q ha hb
    | true =>
      simp only [d354142, d355781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d354143 q = 1) (hb : d355782 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d354143, d355782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d354143, d355782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d354144 q = 1) (hb : d355783 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d354144, d355783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354144, d355783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d354145 q = 1) (hb : d355784 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d354145, d355784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d354145, d355784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d354393 q = 1) (hb : d356033 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d354393, d356033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d354393, d356033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d354394 q = 1) (hb : d356034 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d354394, d356034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d354394, d356034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro96762 (p : Pattern) (ha : d354400 p = 1) (hb : d356040 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d354395 q = 1) (hb : d356035 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d354395, d356035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96761 q ha hb
    | true =>
      simp only [d354395, d356035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96737 q ha hb
  have h2 (q : Pattern) (ha : d354396 q = 1) (hb : d356036 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d354396, d356036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354396, d356036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d354397 q = 1) (hb : d356037 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d354397, d356037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354397, d356037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d354260 q = 1) (hb : d355898 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d354260, d355898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96737 q ha hb
    | true =>
      simp only [d354260, d355898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96719 q ha hb
  have h5 (q : Pattern) (ha : d354261 q = 1) (hb : d355899 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d354261, d355899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354261, d355899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d354262 q = 1) (hb : d355900 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d354262, d355900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354262, d355900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d354398 q = 1) (hb : d356038 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d354398, d356038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d354398, d356038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d354148 q = 1) (hb : d355787 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d354148, d355787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96719 q ha hb
    | true =>
      simp only [d354148, d355787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d354149 q = 1) (hb : d355788 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d354149, d355788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354149, d355788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d354150 q = 1) (hb : d355789 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d354150, d355789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354150, d355789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d354263 q = 1) (hb : d355901 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d354263, d355901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d354263, d355901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d354399 q = 1) (hb : d356039 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d354399, d356039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d354399, d356039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d354400 q = 1) (hb : d356040 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d354400, d356040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d354400, d356040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro96763 (p : Pattern) (ha : d354406 p = 1) (hb : d356046 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d354401 q = 1) (hb : d356041 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d354401, d356041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96762 q ha hb
    | true =>
      simp only [d354401, d356041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d354402 q = 1) (hb : d356042 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d354402, d356042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354402, d356042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d354266 q = 1) (hb : d355904 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d354266, d355904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96738 q ha hb
    | true =>
      simp only [d354266, d355904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d354267 q = 1) (hb : d355905 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d354267, d355905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354267, d355905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d354403 q = 1) (hb : d356043 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d354403, d356043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d354403, d356043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d354404 q = 1) (hb : d356044 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d354404, d356044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d354404, d356044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d354405 q = 1) (hb : d356045 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d354405, d356045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d354405, d356045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d354406 q = 1) (hb : d356046 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d354406, d356046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354406, d356046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro96764 (p : Pattern) (ha : d354412 p = 1) (hb : d356052 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d354266 q = 1) (hb : d355904 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d354266, d355904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96738 q ha hb
    | true =>
      simp only [d354266, d355904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d354267 q = 1) (hb : d355905 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d354267, d355905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354267, d355905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d354409 q = 1) (hb : d356049 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d354409, d356049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d354409, d356049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d354410 q = 1) (hb : d356050 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d354410, d356050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d354410, d356050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d354411 q = 1) (hb : d356051 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d354411, d356051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d354411, d356051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d354412 q = 1) (hb : d356052 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d354412, d356052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354412, d356052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro96765 (p : Pattern) (ha : d354418 p = 1) (hb : d356058 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d354361 q = 1) (hb : d355999 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d354361, d355999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96755 q ha hb
    | true =>
      simp only [d354361, d355999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96733 q ha hb
  have h2 (q : Pattern) (ha : d354362 q = 1) (hb : d356000 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d354362, d356000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354362, d356000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d354363 q = 1) (hb : d356001 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d354363, d356001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d354363, d356001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d354364 q = 1) (hb : d356002 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d354364, d356002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354364, d356002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d354368 q = 1) (hb : d356006 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d354368, d356006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96756 q ha hb
    | true =>
      simp only [d354368, d356006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96734 q ha hb
  have h6 (q : Pattern) (ha : d354369 q = 1) (hb : d356007 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d354369, d356007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354369, d356007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d354370 q = 1) (hb : d356008 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d354370, d356008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d354370, d356008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d354407 q = 1) (hb : d356047 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d354407, d356047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96763 q ha hb
    | true =>
      simp only [d354407, d356047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96739 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d354272 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d354408 q = 1) (hb : d356048 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d354408, d356048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d354408, d356048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d354413 q = 1) (hb : d356053 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d354413, d356053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96764 q ha hb
    | true =>
      simp only [d354413, d356053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d354414 q = 1) (hb : d356054 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d354414, d356054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d354414, d356054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d354415 q = 1) (hb : d356055 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d354415, d356055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d354415, d356055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d354416 q = 1) (hb : d356056 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d354416, d356056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d354416, d356056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d354417 q = 1) (hb : d356057 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d354417, d356057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d354417, d356057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d354418 q = 1) (hb : d356058 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d354418, d356058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354418, d356058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro96766 (p : Pattern) (ha : d354419 p = 1) (hb : d356059 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d354266 q = 1) (hb : d355904 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d354266, d355904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96738 q ha hb
    | true =>
      simp only [d354266, d355904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d354267 q = 1) (hb : d355905 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d354267, d355905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354267, d355905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d354154 q = 1) (hb : d355793 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d354154, d355793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96720 q ha hb
    | true =>
      simp only [d354154, d355793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d354155 q = 1) (hb : d355794 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d354155, d355794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354155, d355794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d354268 q = 1) (hb : d355906 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d354268, d355906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d354268, d355906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d354269 q = 1) (hb : d355907 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d354269, d355907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d354269, d355907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d354359 q = 1) (hb : d355997 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d354359, d355997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354359, d355997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d354419 q = 1) (hb : d356059 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d354419, d356059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d354419, d356059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro96767 (p : Pattern) (ha : d354424 p = 1) (hb : d356064 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d354266 q = 1) (hb : d355904 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d354266, d355904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96738 q ha hb
    | true =>
      simp only [d354266, d355904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d354267 q = 1) (hb : d355905 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d354267, d355905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354267, d355905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d354154 q = 1) (hb : d355793 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d354154, d355793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96720 q ha hb
    | true =>
      simp only [d354154, d355793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d354155 q = 1) (hb : d355794 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d354155, d355794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354155, d355794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d354268 q = 1) (hb : d355906 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d354268, d355906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d354268, d355906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d354365 q = 1) (hb : d356003 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d354365, d356003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354365, d356003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d354366 q = 1) (hb : d356004 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d354366, d356004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d354366, d356004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d354424 q = 1) (hb : d356064 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d354424, d356064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d354424, d356064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro96768 (p : Pattern) (ha : d354428 p = 1) (hb : d356068 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d354401 q = 1) (hb : d356041 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d354401, d356041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96762 q ha hb
    | true =>
      simp only [d354401, d356041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d354402 q = 1) (hb : d356042 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d354402, d356042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354402, d356042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d354266 q = 1) (hb : d355904 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d354266, d355904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96738 q ha hb
    | true =>
      simp only [d354266, d355904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d354267 q = 1) (hb : d355905 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d354267, d355905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354267, d355905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d354403 q = 1) (hb : d356043 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d354403, d356043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d354403, d356043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d354404 q = 1) (hb : d356044 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d354404, d356044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d354404, d356044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d354405 q = 1) (hb : d356045 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d354405, d356045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d354405, d356045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d354428 q = 1) (hb : d356068 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d354428, d356068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d354428, d356068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro96769 (p : Pattern) (ha : d354431 p = 1) (hb : d356071 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d354266 q = 1) (hb : d355904 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d354266, d355904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96738 q ha hb
    | true =>
      simp only [d354266, d355904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d354267 q = 1) (hb : d355905 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d354267, d355905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354267, d355905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d354409 q = 1) (hb : d356049 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d354409, d356049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d354409, d356049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d354410 q = 1) (hb : d356050 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d354410, d356050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d354410, d356050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d354411 q = 1) (hb : d356051 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d354411, d356051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d354411, d356051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d354431 q = 1) (hb : d356071 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d354431, d356071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d354431, d356071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro96770 (p : Pattern) (ha : d354437 p = 1) (hb : d356077 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d354361 q = 1) (hb : d355999 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d354361, d355999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96755 q ha hb
    | true =>
      simp only [d354361, d355999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96733 q ha hb
  have h2 (q : Pattern) (ha : d354362 q = 1) (hb : d356000 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d354362, d356000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354362, d356000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d354363 q = 1) (hb : d356001 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d354363, d356001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d354363, d356001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d354364 q = 1) (hb : d356002 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d354364, d356002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354364, d356002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d354368 q = 1) (hb : d356006 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d354368, d356006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96756 q ha hb
    | true =>
      simp only [d354368, d356006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96734 q ha hb
  have h6 (q : Pattern) (ha : d354369 q = 1) (hb : d356007 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d354369, d356007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354369, d356007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d354370 q = 1) (hb : d356008 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d354370, d356008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d354370, d356008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d354407 q = 1) (hb : d356047 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d354407, d356047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96763 q ha hb
    | true =>
      simp only [d354407, d356047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96739 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d354272 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d354408 q = 1) (hb : d356048 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d354408, d356048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d354408, d356048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d354413 q = 1) (hb : d356053 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d354413, d356053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96764 q ha hb
    | true =>
      simp only [d354413, d356053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d354414 q = 1) (hb : d356054 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d354414, d356054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d354414, d356054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d354415 q = 1) (hb : d356055 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d354415, d356055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d354415, d356055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d354416 q = 1) (hb : d356056 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d354416, d356056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d354416, d356056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d354417 q = 1) (hb : d356057 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d354417, d356057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d354417, d356057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d354420 q = 1) (hb : d356060 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d354420, d356060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96766 q ha hb
    | true =>
      simp only [d354420, d356060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96741 q ha hb
  have h17 (q : Pattern) (ha : d354421 q = 1) (hb : d356061 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d354421, d356061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354421, d356061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d354422 q = 1) (hb : d356062 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d354422, d356062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d354422, d356062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d354423 q = 1) (hb : d356063 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d354423, d356063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354423, d356063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d354425 q = 1) (hb : d356065 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d354425, d356065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96767 q ha hb
    | true =>
      simp only [d354425, d356065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96742 q ha hb
  have h21 (q : Pattern) (ha : d354426 q = 1) (hb : d356066 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d354426, d356066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354426, d356066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d354427 q = 1) (hb : d356067 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d354427, d356067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d354427, d356067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d354429 q = 1) (hb : d356069 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d354429, d356069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96768 q ha hb
    | true =>
      simp only [d354429, d356069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96743 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d354288 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d354430 q = 1) (hb : d356070 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d354430, d356070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d354430, d356070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d354432 q = 1) (hb : d356072 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d354432, d356072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96769 q ha hb
    | true =>
      simp only [d354432, d356072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d354433 q = 1) (hb : d356073 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d354433, d356073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d354433, d356073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d354434 q = 1) (hb : d356074 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d354434, d356074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d354434, d356074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d354435 q = 1) (hb : d356075 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d354435, d356075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d354435, d356075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d354436 q = 1) (hb : d356076 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d354436, d356076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d354436, d356076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d354437 q = 1) (hb : d356077 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d354437, d356077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d354437, d356077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro96771 (p : Pattern) (ha : d354439 p = 1) (hb : d356079 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d354272 q = 1) (hb : d355910 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d354272, d355910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96739 q ha hb
    | true =>
      simp only [d354272, d355910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96721 q ha hb
  have h2 (q : Pattern) (ha : d354344 q = 1) (hb : d355982 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d354344, d355982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354344, d355982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d354345 q = 1) (hb : d355983 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d354345, d355983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d354345, d355983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d354346 q = 1) (hb : d355984 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d354346, d355984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354346, d355984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d354347 q = 1) (hb : d355985 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d354347, d355985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354347, d355985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d354160 q = 1) (hb : d355799 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d354160, d355799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96721 q ha hb
    | true =>
      simp only [d354160, d355799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d354218 q = 1) (hb : d355857 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d354218, d355857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354218, d355857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d354219 q = 1) (hb : d355858 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d354219, d355858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d354219, d355858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d354220 q = 1) (hb : d355859 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d354220, d355859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354220, d355859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d354221 q = 1) (hb : d355860 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d354221, d355860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354221, d355860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d354439 q = 1) (hb : d356079 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d354439, d356079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d354439, d356079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro96772 (p : Pattern) (ha : d354446 p = 1) (hb : d356086 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d354429 q = 1) (hb : d356069 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d354429, d356069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96768 q ha hb
    | true =>
      simp only [d354429, d356069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96743 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d354288 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d354430 q = 1) (hb : d356070 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d354430, d356070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d354430, d356070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d354432 q = 1) (hb : d356072 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d354432, d356072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96769 q ha hb
    | true =>
      simp only [d354432, d356072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d354433 q = 1) (hb : d356073 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d354433, d356073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d354433, d356073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d354434 q = 1) (hb : d356074 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d354434, d356074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d354434, d356074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d354444 q = 1) (hb : d356084 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d354444, d356084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354444, d356084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d354445 q = 1) (hb : d356085 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d354445, d356085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354445, d356085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d354446 q = 1) (hb : d356086 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d354446, d356086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354446, d356086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro96773 (p : Pattern) (ha : d354448 p = 1) (hb : d356088 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d354167 q = 1) (hb : d355806 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d354167, d355806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96723 q ha hb
    | true =>
      simp only [d354167, d355806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d354225 q = 1) (hb : d355864 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d354225, d355864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354225, d355864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d354226 q = 1) (hb : d355865 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d354226, d355865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d354226, d355865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d354227 q = 1) (hb : d355866 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d354227, d355866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354227, d355866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d354228 q = 1) (hb : d355867 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d354228, d355867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354228, d355867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d354448 q = 1) (hb : d356088 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d354448, d356088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354448, d356088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro96774 (p : Pattern) (ha : d354464 p = 1) (hb : d356104 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d354454 q = 1) (hb : d356094 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d354454, d356094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354454, d356094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96759 q ha hb
  have h2 (q : Pattern) (ha : d354381 q = 1) (hb : d356021 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d354381, d356021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96759 q ha hb
    | true =>
      simp only [d354381, d356021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d354455 q = 1) (hb : d356095 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d354455, d356095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d354455, d356095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d354382 q = 1) (hb : d356022 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d354382, d356022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d354382, d356022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d354456 q = 1) (hb : d356096 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d354456, d356096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d354456, d356096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d354457 q = 1) (hb : d356097 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d354457, d356097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d354457, d356097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d354308 q = 1) (hb : d355946 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d354308, d355946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354308, d355946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96736 q ha hb
  have h8 (q : Pattern) (ha : d354254 q = 1) (hb : d355892 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d354254, d355892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96736 q ha hb
    | true =>
      simp only [d354254, d355892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d354309 q = 1) (hb : d355947 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d354309, d355947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d354309, d355947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d354255 q = 1) (hb : d355893 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d354255, d355893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d354255, d355893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d354310 q = 1) (hb : d355948 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d354310, d355948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d354310, d355948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d354311 q = 1) (hb : d355949 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d354311, d355949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d354311, d355949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d354458 q = 1) (hb : d356098 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d354458, d356098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d354458, d356098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d354459 q = 1) (hb : d356099 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d354459, d356099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354459, d356099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96760 q ha hb
  have h15 (q : Pattern) (ha : d354389 q = 1) (hb : d356029 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d354389, d356029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96760 q ha hb
    | true =>
      simp only [d354389, d356029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d354460 q = 1) (hb : d356100 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d354460, d356100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d354460, d356100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d354390 q = 1) (hb : d356030 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d354390, d356030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d354390, d356030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d354461 q = 1) (hb : d356101 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d354461, d356101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d354461, d356101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d354462 q = 1) (hb : d356102 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d354462, d356102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d354462, d356102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d354183 q = 1) (hb : d355822 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d354183, d355822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354183, d355822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96718 q ha hb
  have h21 (q : Pattern) (ha : d354142 q = 1) (hb : d355781 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d354142, d355781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96718 q ha hb
    | true =>
      simp only [d354142, d355781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d354184 q = 1) (hb : d355823 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d354184, d355823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d354184, d355823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d354143 q = 1) (hb : d355782 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d354143, d355782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d354143, d355782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d354185 q = 1) (hb : d355824 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d354185, d355824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d354185, d355824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d354186 q = 1) (hb : d355825 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d354186, d355825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d354186, d355825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h26 (q : Pattern) (ha : d354463 q = 1) (hb : d356103 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d354463, d356103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d354463, d356103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d354464 q = 1) (hb : d356104 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d354464, d356104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d354464, d356104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  exact h27 p ha hb
theorem andIntro96775 (p : Pattern) (ha : d354470 p = 1) (hb : d356110 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d354465 q = 1) (hb : d356105 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d354465, d356105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96774 q ha hb
    | true =>
      simp only [d354465, d356105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96747 q ha hb
  have h2 (q : Pattern) (ha : d354466 q = 1) (hb : d356106 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d354466, d356106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354466, d356106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d354467 q = 1) (hb : d356107 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d354467, d356107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354467, d356107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d354314 q = 1) (hb : d355952 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d354314, d355952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96747 q ha hb
    | true =>
      simp only [d354314, d355952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96726 q ha hb
  have h5 (q : Pattern) (ha : d354315 q = 1) (hb : d355953 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d354315, d355953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354315, d355953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d354316 q = 1) (hb : d355954 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d354316, d355954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354316, d355954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d354468 q = 1) (hb : d356108 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d354468, d356108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d354468, d356108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d354189 q = 1) (hb : d355828 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d354189, d355828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96726 q ha hb
    | true =>
      simp only [d354189, d355828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d354190 q = 1) (hb : d355829 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d354190, d355829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354190, d355829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d354191 q = 1) (hb : d355830 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d354191, d355830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354191, d355830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d354317 q = 1) (hb : d355955 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d354317, d355955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d354317, d355955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d354469 q = 1) (hb : d356109 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d354469, d356109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d354469, d356109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d354470 q = 1) (hb : d356110 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d354470, d356110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d354470, d356110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro96776 (p : Pattern) (ha : d354476 p = 1) (hb : d356116 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d354471 q = 1) (hb : d356111 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d354471, d356111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96775 q ha hb
    | true =>
      simp only [d354471, d356111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d354472 q = 1) (hb : d356112 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d354472, d356112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354472, d356112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d354320 q = 1) (hb : d355958 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d354320, d355958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96748 q ha hb
    | true =>
      simp only [d354320, d355958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d354321 q = 1) (hb : d355959 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d354321, d355959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354321, d355959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d354473 q = 1) (hb : d356113 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d354473, d356113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d354473, d356113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d354474 q = 1) (hb : d356114 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d354474, d356114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d354474, d356114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d354475 q = 1) (hb : d356115 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d354475, d356115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d354475, d356115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d354476 q = 1) (hb : d356116 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d354476, d356116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d354476, d356116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro96777 (p : Pattern) (ha : d354482 p = 1) (hb : d356122 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d354320 q = 1) (hb : d355958 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d354320, d355958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96748 q ha hb
    | true =>
      simp only [d354320, d355958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d354321 q = 1) (hb : d355959 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d354321, d355959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354321, d355959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d354479 q = 1) (hb : d356119 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d354479, d356119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d354479, d356119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d354480 q = 1) (hb : d356120 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d354480, d356120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d354480, d356120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d354481 q = 1) (hb : d356121 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d354481, d356121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d354481, d356121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d354482 q = 1) (hb : d356122 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d354482, d356122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d354482, d356122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro96778 (p : Pattern) (ha : d354488 p = 1) (hb : d356128 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d354477 q = 1) (hb : d356117 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d354477, d356117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96776 q ha hb
    | true =>
      simp only [d354477, d356117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96749 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d354326 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d354478 q = 1) (hb : d356118 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d354478, d356118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d354478, d356118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d354483 q = 1) (hb : d356123 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d354483, d356123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96777 q ha hb
    | true =>
      simp only [d354483, d356123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d354484 q = 1) (hb : d356124 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d354484, d356124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d354484, d356124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d354485 q = 1) (hb : d356125 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d354485, d356125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d354485, d356125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d354486 q = 1) (hb : d356126 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d354486, d356126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354486, d356126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d354487 q = 1) (hb : d356127 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d354487, d356127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354487, d356127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d354488 q = 1) (hb : d356128 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d354488, d356128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354488, d356128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro96779 (p : Pattern) (ha : d354494 p = 1) (hb : d356134 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d354201 q = 1) (hb : d355840 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d354201, d355840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96728 q ha hb
    | true =>
      simp only [d354201, d355840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d354490 q = 1) (hb : d356130 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d354490, d356130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354490, d356130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d354491 q = 1) (hb : d356131 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d354491, d356131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d354491, d356131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d354492 q = 1) (hb : d356132 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d354492, d356132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354492, d356132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d354493 q = 1) (hb : d356133 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d354493, d356133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354493, d356133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d354494 q = 1) (hb : d356134 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d354494, d356134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354494, d356134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro96780 (p : Pattern) (ha : d354500 p = 1) (hb : d356140 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d354349 q = 1) (hb : d355987 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d354349, d355987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354349, d355987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96753 q ha hb
  have h2 (q : Pattern) (ha : d354350 q = 1) (hb : d355988 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d354350, d355988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d354350, d355988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d354356 q = 1) (hb : d355994 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d354356, d355994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96753 q ha hb
    | true =>
      simp only [d354356, d355994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96754 q ha hb
  have h4 (q : Pattern) (ha : d354357 q = 1) (hb : d355995 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d354357, d355995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d354357, d355995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d354358 q = 1) (hb : d355996 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d354358, d355996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d354358, d355996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d354438 q = 1) (hb : d356078 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d354438, d356078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96765 q ha hb
    | true =>
      simp only [d354438, d356078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96770 q ha hb
  have h7 (q : Pattern) (ha : d354440 q = 1) (hb : d356080 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d354440, d356080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96771 q ha hb
    | true =>
      simp only [d354440, d356080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96732 q ha hb
  have h8 (q : Pattern) (ha : d354441 q = 1) (hb : d356081 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d354441, d356081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d354441, d356081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d354442 q = 1) (hb : d356082 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d354442, d356082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d354442, d356082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d354443 q = 1) (hb : d356083 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d354443, d356083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d354443, d356083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d354447 q = 1) (hb : d356087 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d354447, d356087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354447, d356087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96772 q ha hb
  have h12 (q : Pattern) (ha : d354449 q = 1) (hb : d356089 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d354449, d356089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354449, d356089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96773 q ha hb
  have h13 (q : Pattern) (ha : d354450 q = 1) (hb : d356090 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d354450, d356090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d354450, d356090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d354451 q = 1) (hb : d356091 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d354451, d356091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d354451, d356091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d354452 q = 1) (hb : d356092 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d354452, d356092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d354452, d356092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d354453 q = 1) (hb : d356093 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d354453, d356093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d354453, d356093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d354489 q = 1) (hb : d356129 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d354489, d356129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354489, d356129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96778 q ha hb
  have h18 (q : Pattern) (ha : d354495 q = 1) (hb : d356135 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d354495, d356135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354495, d356135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96779 q ha hb
  have h19 (q : Pattern) (ha : d354496 q = 1) (hb : d356136 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d354496, d356136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d354496, d356136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d354497 q = 1) (hb : d356137 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d354497, d356137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d354497, d356137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d354498 q = 1) (hb : d356138 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d354498, d356138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d354498, d356138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d354499 q = 1) (hb : d356139 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d354499, d356139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d354499, d356139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d354500 q = 1) (hb : d356140 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d354500, d356140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d354500, d356140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro96781 (p : Pattern) (ha : d354506 p = 1) (hb : d356146 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d354501 q = 1) (hb : d356141 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d354501, d356141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354501, d356141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96780 q ha hb
  have h2 (q : Pattern) (ha : d354502 q = 1) (hb : d356142 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d354502, d356142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354502, d356142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d354503 q = 1) (hb : d356143 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d354503, d356143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354503, d356143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d354504 q = 1) (hb : d356144 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d354504, d356144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354504, d356144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d354505 q = 1) (hb : d356145 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d354505, d356145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354505, d356145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d354506 q = 1) (hb : d356146 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d354506, d356146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354506, d356146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro96782 (p : Pattern) (ha : d354510 p = 1) (hb : d356150 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d354395 q = 1) (hb : d356035 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d354395, d356035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96761 q ha hb
    | true =>
      simp only [d354395, d356035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96737 q ha hb
  have h2 (q : Pattern) (ha : d354396 q = 1) (hb : d356036 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d354396, d356036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354396, d356036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d354397 q = 1) (hb : d356037 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d354397, d356037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354397, d356037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d354260 q = 1) (hb : d355898 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d354260, d355898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96737 q ha hb
    | true =>
      simp only [d354260, d355898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96719 q ha hb
  have h5 (q : Pattern) (ha : d354261 q = 1) (hb : d355899 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d354261, d355899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354261, d355899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d354262 q = 1) (hb : d355900 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d354262, d355900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354262, d355900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d354398 q = 1) (hb : d356038 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d354398, d356038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d354398, d356038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d354508 q = 1) (hb : d356148 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d354508, d356148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d354508, d356148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d354509 q = 1) (hb : d356149 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d354509, d356149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d354509, d356149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d354510 q = 1) (hb : d356150 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d354510, d356150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d354510, d356150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro96783 (p : Pattern) (ha : d354514 p = 1) (hb : d356154 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d354260 q = 1) (hb : d355898 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d354260, d355898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96737 q ha hb
    | true =>
      simp only [d354260, d355898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96719 q ha hb
  have h2 (q : Pattern) (ha : d354261 q = 1) (hb : d355899 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d354261, d355899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354261, d355899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d354262 q = 1) (hb : d355900 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d354262, d355900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354262, d355900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d354508 q = 1) (hb : d356148 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d354508, d356148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d354508, d356148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d354513 q = 1) (hb : d356153 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d354513, d356153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d354513, d356153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d354514 q = 1) (hb : d356154 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d354514, d356154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d354514, d356154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro96784 (p : Pattern) (ha : d354520 p = 1) (hb : d356160 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d354511 q = 1) (hb : d356151 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d354511, d356151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96782 q ha hb
    | true =>
      simp only [d354511, d356151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d354512 q = 1) (hb : d356152 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d354512, d356152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354512, d356152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d354515 q = 1) (hb : d356155 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d354515, d356155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96783 q ha hb
    | true =>
      simp only [d354515, d356155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d354516 q = 1) (hb : d356156 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d354516, d356156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354516, d356156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d354517 q = 1) (hb : d356157 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d354517, d356157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d354517, d356157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d354518 q = 1) (hb : d356158 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d354518, d356158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d354518, d356158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d354519 q = 1) (hb : d356159 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d354519, d356159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d354519, d356159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d354520 q = 1) (hb : d356160 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d354520, d356160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354520, d356160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro96785 (p : Pattern) (ha : d354524 p = 1) (hb : d356164 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d354515 q = 1) (hb : d356155 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d354515, d356155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96783 q ha hb
    | true =>
      simp only [d354515, d356155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d354516 q = 1) (hb : d356156 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d354516, d356156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354516, d356156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d354521 q = 1) (hb : d356161 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d354521, d356161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d354521, d356161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d354522 q = 1) (hb : d356162 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d354522, d356162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d354522, d356162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d354523 q = 1) (hb : d356163 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d354523, d356163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d354523, d356163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d354524 q = 1) (hb : d356164 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d354524, d356164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354524, d356164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro96786 (p : Pattern) (ha : d354530 p = 1) (hb : d356170 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d354525 q = 1) (hb : d356165 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d354525, d356165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96784 q ha hb
    | true =>
      simp only [d354525, d356165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96785 q ha hb
  have h2 (q : Pattern) (ha : d354526 q = 1) (hb : d356166 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d354526, d356166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354526, d356166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d354527 q = 1) (hb : d356167 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d354527, d356167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d354527, d356167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d354528 q = 1) (hb : d356168 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d354528, d356168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354528, d356168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d354529 q = 1) (hb : d356169 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d354529, d356169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354529, d356169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d354530 q = 1) (hb : d356170 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d354530, d356170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354530, d356170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro96787 (p : Pattern) (ha : d354533 p = 1) (hb : d356173 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d354511 q = 1) (hb : d356151 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d354511, d356151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96782 q ha hb
    | true =>
      simp only [d354511, d356151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d354512 q = 1) (hb : d356152 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d354512, d356152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354512, d356152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d354515 q = 1) (hb : d356155 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d354515, d356155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96783 q ha hb
    | true =>
      simp only [d354515, d356155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d354516 q = 1) (hb : d356156 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d354516, d356156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354516, d356156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d354517 q = 1) (hb : d356157 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d354517, d356157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d354517, d356157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d354518 q = 1) (hb : d356158 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d354518, d356158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d354518, d356158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d354519 q = 1) (hb : d356159 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d354519, d356159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d354519, d356159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d354533 q = 1) (hb : d356173 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d354533, d356173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d354533, d356173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro96788 (p : Pattern) (ha : d354534 p = 1) (hb : d356174 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d354515 q = 1) (hb : d356155 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d354515, d356155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96783 q ha hb
    | true =>
      simp only [d354515, d356155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d354516 q = 1) (hb : d356156 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d354516, d356156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354516, d356156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d354521 q = 1) (hb : d356161 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d354521, d356161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d354521, d356161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d354522 q = 1) (hb : d356162 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d354522, d356162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d354522, d356162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d354523 q = 1) (hb : d356163 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d354523, d356163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d354523, d356163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d354534 q = 1) (hb : d356174 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d354534, d356174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d354534, d356174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro96789 (p : Pattern) (ha : d354540 p = 1) (hb : d356180 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d354525 q = 1) (hb : d356165 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d354525, d356165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96784 q ha hb
    | true =>
      simp only [d354525, d356165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96785 q ha hb
  have h2 (q : Pattern) (ha : d354526 q = 1) (hb : d356166 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d354526, d356166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354526, d356166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d354527 q = 1) (hb : d356167 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d354527, d356167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d354527, d356167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d354528 q = 1) (hb : d356168 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d354528, d356168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354528, d356168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d354529 q = 1) (hb : d356169 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d354529, d356169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354529, d356169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d354535 q = 1) (hb : d356175 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d354535, d356175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96787 q ha hb
    | true =>
      simp only [d354535, d356175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96788 q ha hb
  have h7 (q : Pattern) (ha : d354536 q = 1) (hb : d356176 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d354536, d356176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354536, d356176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d354537 q = 1) (hb : d356177 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d354537, d356177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d354537, d356177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d354538 q = 1) (hb : d356178 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d354538, d356178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354538, d356178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d354539 q = 1) (hb : d356179 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d354539, d356179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354539, d356179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d354540 q = 1) (hb : d356180 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d354540, d356180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d354540, d356180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro96790 (p : Pattern) (ha : d354545 p = 1) (hb : d356185 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d354511 q = 1) (hb : d356151 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d354511, d356151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96782 q ha hb
    | true =>
      simp only [d354511, d356151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d354512 q = 1) (hb : d356152 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d354512, d356152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354512, d356152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d354515 q = 1) (hb : d356155 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d354515, d356155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96783 q ha hb
    | true =>
      simp only [d354515, d356155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d354516 q = 1) (hb : d356156 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d354516, d356156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354516, d356156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d354517 q = 1) (hb : d356157 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d354517, d356157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d354517, d356157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d354518 q = 1) (hb : d356158 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d354518, d356158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d354518, d356158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d354544 q = 1) (hb : d356184 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d354544, d356184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354544, d356184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d354545 q = 1) (hb : d356185 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d354545, d356185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354545, d356185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro96791 (p : Pattern) (ha : d354547 p = 1) (hb : d356187 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d354515 q = 1) (hb : d356155 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d354515, d356155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96783 q ha hb
    | true =>
      simp only [d354515, d356155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d354516 q = 1) (hb : d356156 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d354516, d356156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354516, d356156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d354521 q = 1) (hb : d356161 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d354521, d356161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d354521, d356161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d354522 q = 1) (hb : d356162 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d354522, d356162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d354522, d356162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d354546 q = 1) (hb : d356186 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d354546, d356186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354546, d356186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d354547 q = 1) (hb : d356187 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d354547, d356187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354547, d356187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro96792 (p : Pattern) (ha : d354554 p = 1) (hb : d356194 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d354511 q = 1) (hb : d356151 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d354511, d356151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96782 q ha hb
    | true =>
      simp only [d354511, d356151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d354512 q = 1) (hb : d356152 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d354512, d356152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354512, d356152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d354515 q = 1) (hb : d356155 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d354515, d356155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96783 q ha hb
    | true =>
      simp only [d354515, d356155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d354516 q = 1) (hb : d356156 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d354516, d356156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354516, d356156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d354517 q = 1) (hb : d356157 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d354517, d356157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d354517, d356157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d354552 q = 1) (hb : d356192 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d354552, d356192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354552, d356192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d354553 q = 1) (hb : d356193 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d354553, d356193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d354553, d356193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d354554 q = 1) (hb : d356194 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d354554, d356194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354554, d356194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro96793 (p : Pattern) (ha : d354557 p = 1) (hb : d356197 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d354515 q = 1) (hb : d356155 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d354515, d356155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96783 q ha hb
    | true =>
      simp only [d354515, d356155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d354516 q = 1) (hb : d356156 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d354516, d356156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354516, d356156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d354521 q = 1) (hb : d356161 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d354521, d356161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d354521, d356161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d354555 q = 1) (hb : d356195 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d354555, d356195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354555, d356195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d354556 q = 1) (hb : d356196 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d354556, d356196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d354556, d356196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d354557 q = 1) (hb : d356197 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d354557, d356197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354557, d356197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro96794 (p : Pattern) (ha : d354562 p = 1) (hb : d356201 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d44880 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d46864 q = 1) (hb : d253268 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d46864, d253268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d46864, d253268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d276820 q = 1) (hb : d354372 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d276820, d354372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d276820, d354372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d354561 q = 1) (hb : d356009 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d354561, d356009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354561, d356009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d354562 q = 1) (hb : d356201 q = 1) : d0 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d354562, d356201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354562, d356201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  exact h5 p ha hb
theorem andIntro96795 (p : Pattern) (ha : d354575 p = 1) (hb : d356210 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d354563 q = 1) (hb : d356202 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d354563, d356202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96794 q ha hb
    | true =>
      simp only [d354563, d356202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d354564 q = 1) (hb : d356203 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d354564, d356203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d354564, d356203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d354375 q = 1) (hb : d356011 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d354375, d356011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96758 q ha hb
    | true =>
      simp only [d354375, d356011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d354376 q = 1) (hb : d356012 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d354376, d356012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d354376, d356012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d354565 q = 1) (hb : d356204 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d354565, d356204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d354565, d356204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d354572 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d354573 q = 1) (hb : d356205 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d354573, d356205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d354573, d356205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d354574 q = 1) (hb : d356206 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d354574, d356206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d354574, d356206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d354248 q = 1) (hb : d355886 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d354248, d355886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96735 q ha hb
    | true =>
      simp only [d354248, d355886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d354249 q = 1) (hb : d355887 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d354249, d355887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d354249, d355887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d354377 q = 1) (hb : d356013 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d354377, d356013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d354377, d356013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d354249 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d46871 q = 1) (hb : d354136 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d46871, d354136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96717 q ha hb
    | true =>
      simp only [d46871, d354136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d354137 q = 1) (hb : d355776 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d354137, d355776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d354137, d355776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d354250 q = 1) (hb : d356207 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d354250, d356207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
    | true =>
      simp only [d354250, d356207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d354378 q = 1) (hb : d356208 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d354378, d356208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d354378, d356208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d354379 q = 1) (hb : d356209 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d354379, d356209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d354379, d356209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d354575 q = 1) (hb : d356210 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d354575, d356210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d354575, d356210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro96796 (p : Pattern) (ha : d354580 p = 1) (hb : d356215 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d354375 q = 1) (hb : d356011 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d354375, d356011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96758 q ha hb
    | true =>
      simp only [d354375, d356011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d354376 q = 1) (hb : d356012 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d354376, d356012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d354376, d356012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d354248 q = 1) (hb : d355886 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d354248, d355886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96735 q ha hb
    | true =>
      simp only [d354248, d355886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d354249 q = 1) (hb : d355887 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d354249, d355887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d354249, d355887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d354377 q = 1) (hb : d356013 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d354377, d356013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d354377, d356013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d354248 q = 1) (hb : d356015 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d354248, d356015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96757 q ha hb
    | true =>
      simp only [d354248, d356015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d354249 q = 1) (hb : d356016 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d354249, d356016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d354249, d356016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d46871 q = 1) (hb : d354136 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d46871, d354136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96717 q ha hb
    | true =>
      simp only [d46871, d354136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d354137 q = 1) (hb : d355776 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d354137, d355776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d354137, d355776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d354250 q = 1) (hb : d356017 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d354250, d356017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d354250, d356017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d354378 q = 1) (hb : d356018 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d354378, d356018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d354378, d356018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d354379 q = 1) (hb : d356019 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d354379, d356019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d354379, d356019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d354250 q = 1) (hb : d355888 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d354250, d355888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d354250, d355888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h14 (q : Pattern) (ha : d354386 q = 1) (hb : d356026 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d354386, d356026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d354386, d356026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d354387 q = 1) (hb : d356027 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d354387, d356027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d354387, d356027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d354580 q = 1) (hb : d356215 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d354580, d356215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d354580, d356215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro96797 (p : Pattern) (ha : d354588 p = 1) (hb : d356223 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d354375 q = 1) (hb : d356011 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d354375, d356011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96758 q ha hb
    | true =>
      simp only [d354375, d356011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d354376 q = 1) (hb : d356012 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d354376, d356012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d354376, d356012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d354248 q = 1) (hb : d355886 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d354248, d355886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96735 q ha hb
    | true =>
      simp only [d354248, d355886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d354249 q = 1) (hb : d355887 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d354249, d355887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d354249, d355887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d354377 q = 1) (hb : d356013 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d354377, d356013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d354377, d356013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d354586 q = 1) (hb : d356221 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d354586, d356221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d354586, d356221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d354587 q = 1) (hb : d356222 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d354587, d356222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d354587, d356222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d46871 q = 1) (hb : d354136 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d46871, d354136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96717 q ha hb
    | true =>
      simp only [d46871, d354136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d354137 q = 1) (hb : d355776 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d354137, d355776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d354137, d355776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d354250 q = 1) (hb : d355888 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d354250, d355888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d354250, d355888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d354386 q = 1) (hb : d356026 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d354386, d356026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d354386, d356026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d354387 q = 1) (hb : d356027 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d354387, d356027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d354387, d356027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d354588 q = 1) (hb : d356223 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d354588, d356223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d354588, d356223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro96798 (p : Pattern) (ha : d354594 p = 1) (hb : d356229 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d354576 q = 1) (hb : d356211 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d354576, d356211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96795 q ha hb
    | true =>
      simp only [d354576, d356211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d354577 q = 1) (hb : d356212 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d354577, d356212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d354577, d356212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d354578 q = 1) (hb : d356213 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d354578, d356213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354578, d356213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d354579 q = 1) (hb : d356214 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d354579, d356214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d354579, d356214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d354581 q = 1) (hb : d356216 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d354581, d356216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96796 q ha hb
    | true =>
      simp only [d354581, d356216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d354582 q = 1) (hb : d356217 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d354582, d356217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d354582, d356217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d354583 q = 1) (hb : d356218 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d354583, d356218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354583, d356218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d354584 q = 1) (hb : d356219 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d354584, d356219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d354584, d356219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d354585 q = 1) (hb : d356220 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d354585, d356220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d354585, d356220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d354589 q = 1) (hb : d356224 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d354589, d356224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96797 q ha hb
    | true =>
      simp only [d354589, d356224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d354590 q = 1) (hb : d356225 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d354590, d356225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d354590, d356225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d354591 q = 1) (hb : d356226 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d354591, d356226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354591, d356226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d354592 q = 1) (hb : d356227 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d354592, d356227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d354592, d356227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d354389 q = 1) (hb : d356029 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d354389, d356029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96760 q ha hb
    | true =>
      simp only [d354389, d356029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d354390 q = 1) (hb : d356030 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d354390, d356030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d354390, d356030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d354391 q = 1) (hb : d356031 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d354391, d356031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354391, d356031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d354392 q = 1) (hb : d356032 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d354392, d356032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d354392, d356032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d354593 q = 1) (hb : d356228 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d354593, d356228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d354593, d356228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d354594 q = 1) (hb : d356229 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d354594, d356229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d354594, d356229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro96799 (p : Pattern) (ha : d354598 p = 1) (hb : d356233 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d354389 q = 1) (hb : d356029 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d354389, d356029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96760 q ha hb
    | true =>
      simp only [d354389, d356029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d354390 q = 1) (hb : d356030 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d354390, d356030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d354390, d356030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d354391 q = 1) (hb : d356031 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d354391, d356031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354391, d356031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d354392 q = 1) (hb : d356032 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d354392, d356032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d354392, d356032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d354142 q = 1) (hb : d355781 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d354142, d355781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96718 q ha hb
    | true =>
      simp only [d354142, d355781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d354143 q = 1) (hb : d355782 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d354143, d355782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d354143, d355782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d354144 q = 1) (hb : d355783 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d354144, d355783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354144, d355783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d354145 q = 1) (hb : d355784 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d354145, d355784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d354145, d355784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d354393 q = 1) (hb : d356033 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d354393, d356033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d354393, d356033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d354146 q = 1) (hb : d355785 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d354146, d355785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d354146, d355785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d354598 q = 1) (hb : d356233 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d354598, d356233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d354598, d356233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro96800 (p : Pattern) (ha : d354604 p = 1) (hb : d356239 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d354595 q = 1) (hb : d356230 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d354595, d356230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96798 q ha hb
    | true =>
      simp only [d354595, d356230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96761 q ha hb
  have h2 (q : Pattern) (ha : d354596 q = 1) (hb : d356231 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d354596, d356231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354596, d356231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d354597 q = 1) (hb : d356232 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d354597, d356232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354597, d356232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d354599 q = 1) (hb : d356234 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d354599, d356234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96761 q ha hb
    | true =>
      simp only [d354599, d356234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96799 q ha hb
  have h5 (q : Pattern) (ha : d354600 q = 1) (hb : d356235 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d354600, d356235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354600, d356235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d354601 q = 1) (hb : d356236 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d354601, d356236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354601, d356236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d354602 q = 1) (hb : d356237 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d354602, d356237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d354602, d356237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d354395 q = 1) (hb : d356035 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d354395, d356035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96761 q ha hb
    | true =>
      simp only [d354395, d356035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96737 q ha hb
  have h9 (q : Pattern) (ha : d354396 q = 1) (hb : d356036 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d354396, d356036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354396, d356036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d354397 q = 1) (hb : d356037 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d354397, d356037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354397, d356037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d354260 q = 1) (hb : d355898 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d354260, d355898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96737 q ha hb
    | true =>
      simp only [d354260, d355898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96719 q ha hb
  have h12 (q : Pattern) (ha : d354261 q = 1) (hb : d355899 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d354261, d355899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354261, d355899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d354262 q = 1) (hb : d355900 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d354262, d355900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354262, d355900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d354398 q = 1) (hb : d356038 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d354398, d356038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d354398, d356038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d354603 q = 1) (hb : d356238 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d354603, d356238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d354603, d356238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d354604 q = 1) (hb : d356239 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d354604, d356239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d354604, d356239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h16 p ha hb
theorem andIntro96801 (p : Pattern) (ha : d354610 p = 1) (hb : d356245 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d354605 q = 1) (hb : d356240 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d354605, d356240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96800 q ha hb
    | true =>
      simp only [d354605, d356240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d354606 q = 1) (hb : d356241 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d354606, d356241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354606, d356241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d354511 q = 1) (hb : d356151 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d354511, d356151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96782 q ha hb
    | true =>
      simp only [d354511, d356151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d354512 q = 1) (hb : d356152 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d354512, d356152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354512, d356152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d354607 q = 1) (hb : d356242 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d354607, d356242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d354607, d356242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d354608 q = 1) (hb : d356243 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d354608, d356243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d354608, d356243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d354609 q = 1) (hb : d356244 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d354609, d356244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d354609, d356244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d354610 q = 1) (hb : d356245 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d354610, d356245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354610, d356245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro96802 (p : Pattern) (ha : d354616 p = 1) (hb : d356251 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d354511 q = 1) (hb : d356151 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d354511, d356151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96782 q ha hb
    | true =>
      simp only [d354511, d356151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d354512 q = 1) (hb : d356152 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d354512, d356152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354512, d356152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d354613 q = 1) (hb : d356248 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d354613, d356248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d354613, d356248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d354614 q = 1) (hb : d356249 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d354614, d356249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d354614, d356249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d354615 q = 1) (hb : d356250 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d354615, d356250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d354615, d356250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d354616 q = 1) (hb : d356251 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d354616, d356251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354616, d356251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro96803 (p : Pattern) (ha : d354622 p = 1) (hb : d356257 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d354548 q = 1) (hb : d356188 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d354548, d356188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96790 q ha hb
    | true =>
      simp only [d354548, d356188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96791 q ha hb
  have h2 (q : Pattern) (ha : d354549 q = 1) (hb : d356189 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d354549, d356189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354549, d356189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d354550 q = 1) (hb : d356190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d354550, d356190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d354550, d356190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d354551 q = 1) (hb : d356191 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d354551, d356191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354551, d356191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d354558 q = 1) (hb : d356198 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d354558, d356198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96792 q ha hb
    | true =>
      simp only [d354558, d356198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96793 q ha hb
  have h6 (q : Pattern) (ha : d354559 q = 1) (hb : d356199 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d354559, d356199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354559, d356199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d354560 q = 1) (hb : d356200 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d354560, d356200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d354560, d356200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d354611 q = 1) (hb : d356246 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d354611, d356246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96801 q ha hb
    | true =>
      simp only [d354611, d356246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96784 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d354525 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d354612 q = 1) (hb : d356247 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d354612, d356247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d354612, d356247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d354617 q = 1) (hb : d356252 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d354617, d356252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96802 q ha hb
    | true =>
      simp only [d354617, d356252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d354618 q = 1) (hb : d356253 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d354618, d356253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d354618, d356253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d354619 q = 1) (hb : d356254 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d354619, d356254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d354619, d356254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d354620 q = 1) (hb : d356255 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d354620, d356255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d354620, d356255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d354621 q = 1) (hb : d356256 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d354621, d356256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d354621, d356256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d354622 q = 1) (hb : d356257 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d354622, d356257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354622, d356257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro96804 (p : Pattern) (ha : d354623 p = 1) (hb : d356258 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d354511 q = 1) (hb : d356151 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d354511, d356151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96782 q ha hb
    | true =>
      simp only [d354511, d356151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d354512 q = 1) (hb : d356152 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d354512, d356152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354512, d356152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d354515 q = 1) (hb : d356155 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d354515, d356155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96783 q ha hb
    | true =>
      simp only [d354515, d356155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d354516 q = 1) (hb : d356156 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d354516, d356156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354516, d356156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d354517 q = 1) (hb : d356157 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d354517, d356157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d354517, d356157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d354518 q = 1) (hb : d356158 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d354518, d356158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d354518, d356158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d354544 q = 1) (hb : d356184 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d354544, d356184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354544, d356184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d354623 q = 1) (hb : d356258 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d354623, d356258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d354623, d356258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro96805 (p : Pattern) (ha : d354624 p = 1) (hb : d356259 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d354515 q = 1) (hb : d356155 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d354515, d356155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96783 q ha hb
    | true =>
      simp only [d354515, d356155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d354516 q = 1) (hb : d356156 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d354516, d356156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354516, d356156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d354521 q = 1) (hb : d356161 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d354521, d356161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d354521, d356161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d354522 q = 1) (hb : d356162 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d354522, d356162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d354522, d356162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d354546 q = 1) (hb : d356186 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d354546, d356186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354546, d356186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d354624 q = 1) (hb : d356259 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d354624, d356259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d354624, d356259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro96806 (p : Pattern) (ha : d354629 p = 1) (hb : d356264 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d354511 q = 1) (hb : d356151 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d354511, d356151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96782 q ha hb
    | true =>
      simp only [d354511, d356151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d354512 q = 1) (hb : d356152 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d354512, d356152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354512, d356152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d354515 q = 1) (hb : d356155 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d354515, d356155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96783 q ha hb
    | true =>
      simp only [d354515, d356155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d354516 q = 1) (hb : d356156 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d354516, d356156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354516, d356156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d354517 q = 1) (hb : d356157 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d354517, d356157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d354517, d356157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d354552 q = 1) (hb : d356192 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d354552, d356192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354552, d356192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d354553 q = 1) (hb : d356193 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d354553, d356193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d354553, d356193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d354629 q = 1) (hb : d356264 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d354629, d356264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d354629, d356264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro96807 (p : Pattern) (ha : d354630 p = 1) (hb : d356265 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d354515 q = 1) (hb : d356155 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d354515, d356155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96783 q ha hb
    | true =>
      simp only [d354515, d356155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d354516 q = 1) (hb : d356156 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d354516, d356156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354516, d356156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d354521 q = 1) (hb : d356161 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d354521, d356161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d354521, d356161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d354555 q = 1) (hb : d356195 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d354555, d356195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354555, d356195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d354556 q = 1) (hb : d356196 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d354556, d356196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d354556, d356196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d354630 q = 1) (hb : d356265 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d354630, d356265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d354630, d356265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro96808 (p : Pattern) (ha : d354634 p = 1) (hb : d356269 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d354605 q = 1) (hb : d356240 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d354605, d356240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96800 q ha hb
    | true =>
      simp only [d354605, d356240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d354606 q = 1) (hb : d356241 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d354606, d356241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354606, d356241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d354511 q = 1) (hb : d356151 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d354511, d356151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96782 q ha hb
    | true =>
      simp only [d354511, d356151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d354512 q = 1) (hb : d356152 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d354512, d356152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354512, d356152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d354607 q = 1) (hb : d356242 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d354607, d356242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d354607, d356242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d354608 q = 1) (hb : d356243 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d354608, d356243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d354608, d356243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d354609 q = 1) (hb : d356244 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d354609, d356244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d354609, d356244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d354634 q = 1) (hb : d356269 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d354634, d356269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d354634, d356269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro96809 (p : Pattern) (ha : d354637 p = 1) (hb : d356272 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d354511 q = 1) (hb : d356151 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d354511, d356151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96782 q ha hb
    | true =>
      simp only [d354511, d356151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d354512 q = 1) (hb : d356152 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d354512, d356152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354512, d356152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d354613 q = 1) (hb : d356248 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d354613, d356248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d354613, d356248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d354614 q = 1) (hb : d356249 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d354614, d356249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d354614, d356249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d354615 q = 1) (hb : d356250 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d354615, d356250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d354615, d356250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d354637 q = 1) (hb : d356272 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d354637, d356272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d354637, d356272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro96810 (p : Pattern) (ha : d354643 p = 1) (hb : d356278 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d354548 q = 1) (hb : d356188 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d354548, d356188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96790 q ha hb
    | true =>
      simp only [d354548, d356188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96791 q ha hb
  have h2 (q : Pattern) (ha : d354549 q = 1) (hb : d356189 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d354549, d356189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354549, d356189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d354550 q = 1) (hb : d356190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d354550, d356190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d354550, d356190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d354551 q = 1) (hb : d356191 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d354551, d356191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354551, d356191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d354558 q = 1) (hb : d356198 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d354558, d356198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96792 q ha hb
    | true =>
      simp only [d354558, d356198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96793 q ha hb
  have h6 (q : Pattern) (ha : d354559 q = 1) (hb : d356199 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d354559, d356199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354559, d356199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d354560 q = 1) (hb : d356200 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d354560, d356200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d354560, d356200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d354611 q = 1) (hb : d356246 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d354611, d356246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96801 q ha hb
    | true =>
      simp only [d354611, d356246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96784 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d354525 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d354612 q = 1) (hb : d356247 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d354612, d356247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d354612, d356247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d354617 q = 1) (hb : d356252 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d354617, d356252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96802 q ha hb
    | true =>
      simp only [d354617, d356252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d354618 q = 1) (hb : d356253 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d354618, d356253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d354618, d356253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d354619 q = 1) (hb : d356254 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d354619, d356254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d354619, d356254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d354620 q = 1) (hb : d356255 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d354620, d356255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d354620, d356255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d354621 q = 1) (hb : d356256 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d354621, d356256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d354621, d356256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d354625 q = 1) (hb : d356260 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d354625, d356260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96804 q ha hb
    | true =>
      simp only [d354625, d356260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96805 q ha hb
  have h17 (q : Pattern) (ha : d354626 q = 1) (hb : d356261 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d354626, d356261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354626, d356261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d354627 q = 1) (hb : d356262 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d354627, d356262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d354627, d356262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d354628 q = 1) (hb : d356263 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d354628, d356263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354628, d356263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d354631 q = 1) (hb : d356266 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d354631, d356266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96806 q ha hb
    | true =>
      simp only [d354631, d356266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96807 q ha hb
  have h21 (q : Pattern) (ha : d354632 q = 1) (hb : d356267 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d354632, d356267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354632, d356267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d354633 q = 1) (hb : d356268 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d354633, d356268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d354633, d356268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d354635 q = 1) (hb : d356270 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d354635, d356270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96808 q ha hb
    | true =>
      simp only [d354635, d356270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96787 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d354535 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d354636 q = 1) (hb : d356271 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d354636, d356271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d354636, d356271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d354638 q = 1) (hb : d356273 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d354638, d356273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96809 q ha hb
    | true =>
      simp only [d354638, d356273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d354639 q = 1) (hb : d356274 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d354639, d356274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d354639, d356274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d354640 q = 1) (hb : d356275 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d354640, d356275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d354640, d356275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d354641 q = 1) (hb : d356276 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d354641, d356276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d354641, d356276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d354642 q = 1) (hb : d356277 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d354642, d356277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d354642, d356277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d354643 q = 1) (hb : d356278 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d354643, d356278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d354643, d356278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro96811 (p : Pattern) (ha : d354650 p = 1) (hb : d356285 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d354525 q = 1) (hb : d356165 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d354525, d356165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96784 q ha hb
    | true =>
      simp only [d354525, d356165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96785 q ha hb
  have h2 (q : Pattern) (ha : d354526 q = 1) (hb : d356166 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d354526, d356166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354526, d356166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d354527 q = 1) (hb : d356167 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d354527, d356167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d354527, d356167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d354528 q = 1) (hb : d356168 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d354528, d356168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354528, d356168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d354529 q = 1) (hb : d356169 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d354529, d356169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354529, d356169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d354645 q = 1) (hb : d356280 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d354645, d356280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96785 q ha hb
    | true =>
      simp only [d354645, d356280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d354646 q = 1) (hb : d356281 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d354646, d356281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354646, d356281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d354647 q = 1) (hb : d356282 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d354647, d356282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d354647, d356282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d354648 q = 1) (hb : d356283 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d354648, d356283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354648, d356283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d354649 q = 1) (hb : d356284 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d354649, d356284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354649, d356284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d354650 q = 1) (hb : d356285 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d354650, d356285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d354650, d356285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro96812 (p : Pattern) (ha : d354656 p = 1) (hb : d356291 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d354645 q = 1) (hb : d356280 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d354645, d356280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96785 q ha hb
    | true =>
      simp only [d354645, d356280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d354646 q = 1) (hb : d356281 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d354646, d356281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354646, d356281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d354647 q = 1) (hb : d356282 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d354647, d356282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d354647, d356282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d354648 q = 1) (hb : d356283 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d354648, d356283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354648, d356283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d354649 q = 1) (hb : d356284 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d354649, d356284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354649, d356284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d354651 q = 1) (hb : d356286 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d354651, d356286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96788 q ha hb
    | true =>
      simp only [d354651, d356286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d354652 q = 1) (hb : d356287 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d354652, d356287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354652, d356287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d354653 q = 1) (hb : d356288 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d354653, d356288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d354653, d356288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d354654 q = 1) (hb : d356289 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d354654, d356289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354654, d356289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d354655 q = 1) (hb : d356290 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d354655, d356290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354655, d356290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d354656 q = 1) (hb : d356291 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d354656, d356291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d354656, d356291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro96813 (p : Pattern) (ha : d354663 p = 1) (hb : d356298 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d354635 q = 1) (hb : d356270 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d354635, d356270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96808 q ha hb
    | true =>
      simp only [d354635, d356270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96787 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d354535 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d354636 q = 1) (hb : d356271 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d354636, d356271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d354636, d356271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d354638 q = 1) (hb : d356273 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d354638, d356273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96809 q ha hb
    | true =>
      simp only [d354638, d356273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d354639 q = 1) (hb : d356274 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d354639, d356274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d354639, d356274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d354640 q = 1) (hb : d356275 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d354640, d356275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d354640, d356275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d354661 q = 1) (hb : d356296 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d354661, d356296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354661, d356296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d354662 q = 1) (hb : d356297 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d354662, d356297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354662, d356297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d354663 q = 1) (hb : d356298 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d354663, d356298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354663, d356298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro96814 (p : Pattern) (ha : d354665 p = 1) (hb : d356300 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d354651 q = 1) (hb : d356286 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d354651, d356286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96788 q ha hb
    | true =>
      simp only [d354651, d356286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d354652 q = 1) (hb : d356287 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d354652, d356287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354652, d356287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d354653 q = 1) (hb : d356288 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d354653, d356288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d354653, d356288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d354654 q = 1) (hb : d356289 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d354654, d356289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354654, d356289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d354655 q = 1) (hb : d356290 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d354655, d356290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354655, d356290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d354665 q = 1) (hb : d356300 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d354665, d356300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354665, d356300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro96815 (p : Pattern) (ha : d354685 p = 1) (hb : d356320 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d354671 q = 1) (hb : d356306 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d354671, d356306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354671, d356306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96795 q ha hb
  have h2 (q : Pattern) (ha : d354576 q = 1) (hb : d356211 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d354576, d356211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96795 q ha hb
    | true =>
      simp only [d354576, d356211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d354672 q = 1) (hb : d356307 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d354672, d356307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d354672, d356307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d354577 q = 1) (hb : d356212 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d354577, d356212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d354577, d356212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d354673 q = 1) (hb : d356308 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d354673, d356308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d354673, d356308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d354674 q = 1) (hb : d356309 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d354674, d356309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d354674, d356309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d354675 q = 1) (hb : d356310 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d354675, d356310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354675, d356310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96796 q ha hb
  have h8 (q : Pattern) (ha : d354581 q = 1) (hb : d356216 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d354581, d356216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96796 q ha hb
    | true =>
      simp only [d354581, d356216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d354676 q = 1) (hb : d356311 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d354676, d356311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d354676, d356311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d354582 q = 1) (hb : d356217 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d354582, d356217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d354582, d356217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d354677 q = 1) (hb : d356312 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d354677, d356312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d354677, d356312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d354678 q = 1) (hb : d356313 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d354678, d356313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d354678, d356313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d354679 q = 1) (hb : d356314 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d354679, d356314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d354679, d356314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d354680 q = 1) (hb : d356315 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d354680, d356315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354680, d356315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96797 q ha hb
  have h15 (q : Pattern) (ha : d354589 q = 1) (hb : d356224 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d354589, d356224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96797 q ha hb
    | true =>
      simp only [d354589, d356224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d354681 q = 1) (hb : d356316 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d354681, d356316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d354681, d356316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d354590 q = 1) (hb : d356225 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d354590, d356225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d354590, d356225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d354682 q = 1) (hb : d356317 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d354682, d356317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d354682, d356317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d354683 q = 1) (hb : d356318 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d354683, d356318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d354683, d356318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d354459 q = 1) (hb : d356099 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d354459, d356099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354459, d356099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96760 q ha hb
  have h21 (q : Pattern) (ha : d354389 q = 1) (hb : d356029 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d354389, d356029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96760 q ha hb
    | true =>
      simp only [d354389, d356029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d354460 q = 1) (hb : d356100 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d354460, d356100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d354460, d356100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d354390 q = 1) (hb : d356030 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d354390, d356030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d354390, d356030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d354461 q = 1) (hb : d356101 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d354461, d356101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d354461, d356101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d354462 q = 1) (hb : d356102 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d354462, d356102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d354462, d356102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h26 (q : Pattern) (ha : d354684 q = 1) (hb : d356319 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d354684, d356319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d354684, d356319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d354685 q = 1) (hb : d356320 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d354685, d356320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d354685, d356320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  exact h27 p ha hb
theorem andIntro96816 (p : Pattern) (ha : d354689 p = 1) (hb : d356324 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d354459 q = 1) (hb : d356099 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d354459, d356099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354459, d356099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96760 q ha hb
  have h2 (q : Pattern) (ha : d354389 q = 1) (hb : d356029 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d354389, d356029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96760 q ha hb
    | true =>
      simp only [d354389, d356029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d354460 q = 1) (hb : d356100 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d354460, d356100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d354460, d356100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d354390 q = 1) (hb : d356030 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d354390, d356030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d354390, d356030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d354461 q = 1) (hb : d356101 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d354461, d356101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d354461, d356101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d354462 q = 1) (hb : d356102 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d354462, d356102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d354462, d356102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d354183 q = 1) (hb : d355822 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d354183, d355822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354183, d355822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96718 q ha hb
  have h8 (q : Pattern) (ha : d354142 q = 1) (hb : d355781 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d354142, d355781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96718 q ha hb
    | true =>
      simp only [d354142, d355781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d354184 q = 1) (hb : d355823 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d354184, d355823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d354184, d355823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d354143 q = 1) (hb : d355782 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d354143, d355782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d354143, d355782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d354185 q = 1) (hb : d355824 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d354185, d355824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d354185, d355824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d354186 q = 1) (hb : d355825 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d354186, d355825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d354186, d355825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d354463 q = 1) (hb : d356103 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d354463, d356103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d354463, d356103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d354187 q = 1) (hb : d355826 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d354187, d355826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d354187, d355826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d354689 q = 1) (hb : d356324 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d354689, d356324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d354689, d356324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro96817 (p : Pattern) (ha : d354695 p = 1) (hb : d356330 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d354686 q = 1) (hb : d356321 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d354686, d356321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96815 q ha hb
    | true =>
      simp only [d354686, d356321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96774 q ha hb
  have h2 (q : Pattern) (ha : d354687 q = 1) (hb : d356322 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d354687, d356322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354687, d356322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d354688 q = 1) (hb : d356323 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d354688, d356323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354688, d356323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d354690 q = 1) (hb : d356325 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d354690, d356325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96774 q ha hb
    | true =>
      simp only [d354690, d356325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96816 q ha hb
  have h5 (q : Pattern) (ha : d354691 q = 1) (hb : d356326 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d354691, d356326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354691, d356326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d354692 q = 1) (hb : d356327 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d354692, d356327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354692, d356327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d354693 q = 1) (hb : d356328 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d354693, d356328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d354693, d356328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d354465 q = 1) (hb : d356105 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d354465, d356105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96774 q ha hb
    | true =>
      simp only [d354465, d356105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96747 q ha hb
  have h9 (q : Pattern) (ha : d354466 q = 1) (hb : d356106 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d354466, d356106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354466, d356106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d354467 q = 1) (hb : d356107 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d354467, d356107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354467, d356107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d354314 q = 1) (hb : d355952 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d354314, d355952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96747 q ha hb
    | true =>
      simp only [d354314, d355952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96726 q ha hb
  have h12 (q : Pattern) (ha : d354315 q = 1) (hb : d355953 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d354315, d355953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354315, d355953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d354316 q = 1) (hb : d355954 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d354316, d355954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354316, d355954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d354468 q = 1) (hb : d356108 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d354468, d356108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d354468, d356108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d354694 q = 1) (hb : d356329 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d354694, d356329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d354694, d356329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d354695 q = 1) (hb : d356330 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d354695, d356330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d354695, d356330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h16 p ha hb
theorem andIntro96818 (p : Pattern) (ha : d354700 p = 1) (hb : d356335 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d354465 q = 1) (hb : d356105 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d354465, d356105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96774 q ha hb
    | true =>
      simp only [d354465, d356105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96747 q ha hb
  have h2 (q : Pattern) (ha : d354466 q = 1) (hb : d356106 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d354466, d356106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354466, d356106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d354467 q = 1) (hb : d356107 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d354467, d356107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354467, d356107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d354314 q = 1) (hb : d355952 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d354314, d355952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96747 q ha hb
    | true =>
      simp only [d354314, d355952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96726 q ha hb
  have h5 (q : Pattern) (ha : d354315 q = 1) (hb : d355953 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d354315, d355953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354315, d355953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d354316 q = 1) (hb : d355954 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d354316, d355954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354316, d355954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d354468 q = 1) (hb : d356108 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d354468, d356108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d354468, d356108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d354698 q = 1) (hb : d356333 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d354698, d356333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d354698, d356333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d354699 q = 1) (hb : d356334 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d354699, d356334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d354699, d356334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d354700 q = 1) (hb : d356335 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d354700, d356335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d354700, d356335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro96819 (p : Pattern) (ha : d354706 p = 1) (hb : d356341 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d354696 q = 1) (hb : d356331 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d354696, d356331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96817 q ha hb
    | true =>
      simp only [d354696, d356331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d354697 q = 1) (hb : d356332 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d354697, d356332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354697, d356332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d354701 q = 1) (hb : d356336 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d354701, d356336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96818 q ha hb
    | true =>
      simp only [d354701, d356336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d354702 q = 1) (hb : d356337 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d354702, d356337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354702, d356337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d354703 q = 1) (hb : d356338 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d354703, d356338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d354703, d356338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d354704 q = 1) (hb : d356339 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d354704, d356339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d354704, d356339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d354705 q = 1) (hb : d356340 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d354705, d356340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d354705, d356340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d354706 q = 1) (hb : d356341 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d354706, d356341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d354706, d356341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro96820 (p : Pattern) (ha : d354708 p = 1) (hb : d356343 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d354314 q = 1) (hb : d355952 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d354314, d355952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96747 q ha hb
    | true =>
      simp only [d354314, d355952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96726 q ha hb
  have h2 (q : Pattern) (ha : d354315 q = 1) (hb : d355953 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d354315, d355953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354315, d355953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d354316 q = 1) (hb : d355954 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d354316, d355954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354316, d355954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d354698 q = 1) (hb : d356333 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d354698, d356333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d354698, d356333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d354707 q = 1) (hb : d356342 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d354707, d356342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d354707, d356342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d354708 q = 1) (hb : d356343 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d354708, d356343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d354708, d356343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro96821 (p : Pattern) (ha : d354714 p = 1) (hb : d356349 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d354701 q = 1) (hb : d356336 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d354701, d356336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96818 q ha hb
    | true =>
      simp only [d354701, d356336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d354702 q = 1) (hb : d356337 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d354702, d356337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354702, d356337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d354709 q = 1) (hb : d356344 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d354709, d356344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96820 q ha hb
    | true =>
      simp only [d354709, d356344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d354710 q = 1) (hb : d356345 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d354710, d356345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354710, d356345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d354711 q = 1) (hb : d356346 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d354711, d356346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d354711, d356346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d354712 q = 1) (hb : d356347 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d354712, d356347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d354712, d356347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d354713 q = 1) (hb : d356348 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d354713, d356348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d354713, d356348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d354714 q = 1) (hb : d356349 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d354714, d356349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d354714, d356349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro96822 (p : Pattern) (ha : d354725 p = 1) (hb : d356355 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d354701 q = 1) (hb : d356336 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d354701, d356336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96818 q ha hb
    | true =>
      simp only [d354701, d356336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d354702 q = 1) (hb : d356337 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d354702, d356337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354702, d356337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d354722 q = 1) (hb : d356352 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d354722, d356352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d354722, d356352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d354723 q = 1) (hb : d356353 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d354723, d356353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d354723, d356353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d354724 q = 1) (hb : d356354 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d354724, d356354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d354724, d356354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d354725 q = 1) (hb : d356355 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d354725, d356355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d354725, d356355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro96823 (p : Pattern) (ha : d354731 p = 1) (hb : d356361 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d354715 q = 1) (hb : d356350 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d354715, d356350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96819 q ha hb
    | true =>
      simp only [d354715, d356350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96821 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d354720 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d354721 q = 1) (hb : d356351 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d354721, d356351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d354721, d356351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d354726 q = 1) (hb : d356356 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d354726, d356356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96822 q ha hb
    | true =>
      simp only [d354726, d356356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d354727 q = 1) (hb : d356357 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d354727, d356357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d354727, d356357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d354728 q = 1) (hb : d356358 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d354728, d356358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d354728, d356358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d354729 q = 1) (hb : d356359 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d354729, d356359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354729, d356359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d354730 q = 1) (hb : d356360 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d354730, d356360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354730, d356360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d354731 q = 1) (hb : d356361 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d354731, d356361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354731, d356361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro96824 (p : Pattern) (ha : d354719 p = 1) (hb : d356366 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d354709 q = 1) (hb : d356344 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d354709, d356344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96820 q ha hb
    | true =>
      simp only [d354709, d356344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d354710 q = 1) (hb : d356345 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d354710, d356345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354710, d356345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d354716 q = 1) (hb : d356363 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d354716, d356363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d354716, d356363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d354717 q = 1) (hb : d356364 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d354717, d356364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d354717, d356364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d354718 q = 1) (hb : d356365 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d354718, d356365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d354718, d356365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d354719 q = 1) (hb : d356366 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d354719, d356366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d354719, d356366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro96825 (p : Pattern) (ha : d354738 p = 1) (hb : d356372 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d354733 q = 1) (hb : d356367 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d354733, d356367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96824 q ha hb
    | true =>
      simp only [d354733, d356367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d354734 q = 1) (hb : d356368 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d354734, d356368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354734, d356368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d354735 q = 1) (hb : d356369 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d354735, d356369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d354735, d356369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d354736 q = 1) (hb : d356370 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d354736, d356370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354736, d356370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d354737 q = 1) (hb : d356371 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d354737, d356371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354737, d356371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d354738 q = 1) (hb : d356372 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d354738, d356372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354738, d356372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro96826 (p : Pattern) (ha : d354744 p = 1) (hb : d356378 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d354531 q = 1) (hb : d356171 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d354531, d356171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354531, d356171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96786 q ha hb
  have h2 (q : Pattern) (ha : d354532 q = 1) (hb : d356172 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d354532, d356172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d354532, d356172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d354541 q = 1) (hb : d356181 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d354541, d356181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96786 q ha hb
    | true =>
      simp only [d354541, d356181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96789 q ha hb
  have h4 (q : Pattern) (ha : d354542 q = 1) (hb : d356182 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d354542, d356182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d354542, d356182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d354543 q = 1) (hb : d356183 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d354543, d356183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d354543, d356183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d354644 q = 1) (hb : d356279 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d354644, d356279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96803 q ha hb
    | true =>
      simp only [d354644, d356279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96810 q ha hb
  have h7 (q : Pattern) (ha : d354657 q = 1) (hb : d356292 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d354657, d356292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96811 q ha hb
    | true =>
      simp only [d354657, d356292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96812 q ha hb
  have h8 (q : Pattern) (ha : d354658 q = 1) (hb : d356293 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d354658, d356293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d354658, d356293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d354659 q = 1) (hb : d356294 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d354659, d356294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d354659, d356294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d354660 q = 1) (hb : d356295 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d354660, d356295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d354660, d356295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d354664 q = 1) (hb : d356299 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d354664, d356299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354664, d356299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96813 q ha hb
  have h12 (q : Pattern) (ha : d354666 q = 1) (hb : d356301 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d354666, d356301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354666, d356301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96814 q ha hb
  have h13 (q : Pattern) (ha : d354667 q = 1) (hb : d356302 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d354667, d356302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d354667, d356302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d354668 q = 1) (hb : d356303 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d354668, d356303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d354668, d356303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d354669 q = 1) (hb : d356304 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d354669, d356304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d354669, d356304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d354670 q = 1) (hb : d356305 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d354670, d356305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d354670, d356305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d354732 q = 1) (hb : d356362 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d354732, d356362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354732, d356362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96823 q ha hb
  have h18 (q : Pattern) (ha : d354739 q = 1) (hb : d356373 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d354739, d356373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354739, d356373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96825 q ha hb
  have h19 (q : Pattern) (ha : d354740 q = 1) (hb : d356374 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d354740, d356374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d354740, d356374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d354741 q = 1) (hb : d356375 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d354741, d356375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d354741, d356375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d354742 q = 1) (hb : d356376 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d354742, d356376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d354742, d356376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d354743 q = 1) (hb : d356377 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d354743, d356377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d354743, d356377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d354744 q = 1) (hb : d356378 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d354744, d356378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d354744, d356378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro96827 (p : Pattern) (ha : d354750 p = 1) (hb : d356384 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d354745 q = 1) (hb : d356379 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d354745, d356379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354745, d356379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96826 q ha hb
  have h2 (q : Pattern) (ha : d354746 q = 1) (hb : d356380 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d354746, d356380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354746, d356380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d354747 q = 1) (hb : d356381 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d354747, d356381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354747, d356381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d354748 q = 1) (hb : d356382 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d354748, d356382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354748, d356382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d354749 q = 1) (hb : d356383 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d354749, d356383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354749, d356383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d354750 q = 1) (hb : d356384 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d354750, d356384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354750, d356384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro96828 (p : Pattern) (ha : d354753 p = 1) (hb : d356387 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d354248 q = 1) (hb : d355886 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d354248, d355886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96735 q ha hb
    | true =>
      simp only [d354248, d355886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d354249 q = 1) (hb : d355887 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d354249, d355887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d354249, d355887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d46871 q = 1) (hb : d354136 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d46871, d354136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96717 q ha hb
    | true =>
      simp only [d46871, d354136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d354137 q = 1) (hb : d355776 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d354137, d355776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d354137, d355776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d354250 q = 1) (hb : d355888 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d354250, d355888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d354250, d355888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d354138 q = 1) (hb : d355777 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d354138, d355777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d354138, d355777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d354251 q = 1) (hb : d355889 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d354251, d355889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d354251, d355889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d354252 q = 1) (hb : d355890 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d354252, d355890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d354252, d355890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d354753 q = 1) (hb : d356387 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d354753, d356387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d354753, d356387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h9 p ha hb
theorem andIntro96829 (p : Pattern) (ha : d354759 p = 1) (hb : d356393 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d354576 q = 1) (hb : d356211 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d354576, d356211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96795 q ha hb
    | true =>
      simp only [d354576, d356211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d354577 q = 1) (hb : d356212 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d354577, d356212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d354577, d356212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d354578 q = 1) (hb : d356213 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d354578, d356213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354578, d356213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d354579 q = 1) (hb : d356214 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d354579, d356214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d354579, d356214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d354581 q = 1) (hb : d356216 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d354581, d356216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96796 q ha hb
    | true =>
      simp only [d354581, d356216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d354582 q = 1) (hb : d356217 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d354582, d356217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d354582, d356217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d354583 q = 1) (hb : d356218 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d354583, d356218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354583, d356218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d354584 q = 1) (hb : d356219 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d354584, d356219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d354584, d356219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d354585 q = 1) (hb : d356220 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d354585, d356220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d354585, d356220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d354589 q = 1) (hb : d356224 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d354589, d356224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96797 q ha hb
    | true =>
      simp only [d354589, d356224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d354590 q = 1) (hb : d356225 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d354590, d356225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d354590, d356225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d354591 q = 1) (hb : d356226 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d354591, d356226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354591, d356226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d354592 q = 1) (hb : d356227 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d354592, d356227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d354592, d356227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d354754 q = 1) (hb : d356388 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d354754, d356388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96828 q ha hb
    | true =>
      simp only [d354754, d356388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d354755 q = 1) (hb : d356389 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d354755, d356389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d354755, d356389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d354756 q = 1) (hb : d356390 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d354756, d356390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354756, d356390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d354757 q = 1) (hb : d356391 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d354757, d356391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d354757, d356391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d354758 q = 1) (hb : d356392 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d354758, d356392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d354758, d356392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d354759 q = 1) (hb : d356393 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d354759, d356393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d354759, d356393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro96830 (p : Pattern) (ha : d354762 p = 1) (hb : d356396 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d354381 q = 1) (hb : d356021 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d354381, d356021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96759 q ha hb
    | true =>
      simp only [d354381, d356021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d354382 q = 1) (hb : d356022 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d354382, d356022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d354382, d356022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d354383 q = 1) (hb : d356023 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d354383, d356023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354383, d356023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d354384 q = 1) (hb : d356024 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d354384, d356024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d354384, d356024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d354754 q = 1) (hb : d356388 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d354754, d356388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96828 q ha hb
    | true =>
      simp only [d354754, d356388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d354755 q = 1) (hb : d356389 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d354755, d356389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d354755, d356389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d354756 q = 1) (hb : d356390 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d354756, d356390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354756, d356390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d354757 q = 1) (hb : d356391 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d354757, d356391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d354757, d356391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d354760 q = 1) (hb : d356394 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d354760, d356394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d354760, d356394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d354761 q = 1) (hb : d356395 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d354761, d356395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d354761, d356395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d354762 q = 1) (hb : d356396 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d354762, d356396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d354762, d356396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro96831 (p : Pattern) (ha : d354766 p = 1) (hb : d356400 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d354754 q = 1) (hb : d356388 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d354754, d356388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96828 q ha hb
    | true =>
      simp only [d354754, d356388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d354755 q = 1) (hb : d356389 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d354755, d356389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d354755, d356389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d354756 q = 1) (hb : d356390 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d354756, d356390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354756, d356390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d354757 q = 1) (hb : d356391 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d354757, d356391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d354757, d356391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d354761 q = 1) (hb : d356395 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d354761, d356395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d354761, d356395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d354766 q = 1) (hb : d356400 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d354766, d356400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d354766, d356400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro96832 (p : Pattern) (ha : d354773 p = 1) (hb : d356407 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d354763 q = 1) (hb : d356397 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d354763, d356397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96829 q ha hb
    | true =>
      simp only [d354763, d356397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96830 q ha hb
  have h2 (q : Pattern) (ha : d354764 q = 1) (hb : d356398 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d354764, d356398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354764, d356398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d354765 q = 1) (hb : d356399 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d354765, d356399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354765, d356399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d354767 q = 1) (hb : d356401 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d354767, d356401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96830 q ha hb
    | true =>
      simp only [d354767, d356401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96831 q ha hb
  have h5 (q : Pattern) (ha : d354768 q = 1) (hb : d356402 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d354768, d356402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354768, d356402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d354769 q = 1) (hb : d356403 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d354769, d356403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354769, d356403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d354770 q = 1) (hb : d356404 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d354770, d356404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d354770, d356404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d354771 q = 1) (hb : d356405 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d354771, d356405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d354771, d356405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d354772 q = 1) (hb : d356406 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d354772, d356406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d354772, d356406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d354773 q = 1) (hb : d356407 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d354773, d356407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d354773, d356407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro96833 (p : Pattern) (ha : d354777 p = 1) (hb : d356411 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d354767 q = 1) (hb : d356401 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d354767, d356401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96830 q ha hb
    | true =>
      simp only [d354767, d356401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96831 q ha hb
  have h2 (q : Pattern) (ha : d354768 q = 1) (hb : d356402 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d354768, d356402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354768, d356402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d354769 q = 1) (hb : d356403 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d354769, d356403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354769, d356403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d354771 q = 1) (hb : d356405 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d354771, d356405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d354771, d356405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d354776 q = 1) (hb : d356410 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d354776, d356410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d354776, d356410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d354777 q = 1) (hb : d356411 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d354777, d356411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d354777, d356411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro96834 (p : Pattern) (ha : d354783 p = 1) (hb : d356417 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d354774 q = 1) (hb : d356408 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d354774, d356408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96832 q ha hb
    | true =>
      simp only [d354774, d356408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d354775 q = 1) (hb : d356409 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d354775, d356409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354775, d356409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d354778 q = 1) (hb : d356412 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d354778, d356412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96833 q ha hb
    | true =>
      simp only [d354778, d356412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d354779 q = 1) (hb : d356413 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d354779, d356413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354779, d356413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d354780 q = 1) (hb : d356414 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d354780, d356414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d354780, d356414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d354781 q = 1) (hb : d356415 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d354781, d356415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d354781, d356415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d354782 q = 1) (hb : d356416 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d354782, d356416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d354782, d356416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d354783 q = 1) (hb : d356417 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d354783, d356417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354783, d356417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro96835 (p : Pattern) (ha : d354787 p = 1) (hb : d356421 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d354778 q = 1) (hb : d356412 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d354778, d356412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96833 q ha hb
    | true =>
      simp only [d354778, d356412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d354779 q = 1) (hb : d356413 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d354779, d356413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354779, d356413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d354784 q = 1) (hb : d356418 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d354784, d356418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d354784, d356418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d354785 q = 1) (hb : d356419 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d354785, d356419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d354785, d356419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d354786 q = 1) (hb : d356420 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d354786, d356420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d354786, d356420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d354787 q = 1) (hb : d356421 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d354787, d356421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354787, d356421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro96836 (p : Pattern) (ha : d354793 p = 1) (hb : d356427 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d354788 q = 1) (hb : d356422 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d354788, d356422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96834 q ha hb
    | true =>
      simp only [d354788, d356422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96835 q ha hb
  have h2 (q : Pattern) (ha : d354789 q = 1) (hb : d356423 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d354789, d356423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354789, d356423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d354790 q = 1) (hb : d356424 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d354790, d356424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d354790, d356424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d354791 q = 1) (hb : d356425 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d354791, d356425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354791, d356425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d354792 q = 1) (hb : d356426 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d354792, d356426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354792, d356426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d354793 q = 1) (hb : d356427 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d354793, d356427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354793, d356427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro96837 (p : Pattern) (ha : d354796 p = 1) (hb : d356430 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d354774 q = 1) (hb : d356408 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d354774, d356408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96832 q ha hb
    | true =>
      simp only [d354774, d356408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d354775 q = 1) (hb : d356409 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d354775, d356409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354775, d356409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d354778 q = 1) (hb : d356412 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d354778, d356412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96833 q ha hb
    | true =>
      simp only [d354778, d356412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d354779 q = 1) (hb : d356413 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d354779, d356413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354779, d356413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d354780 q = 1) (hb : d356414 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d354780, d356414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d354780, d356414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d354781 q = 1) (hb : d356415 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d354781, d356415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d354781, d356415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d354782 q = 1) (hb : d356416 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d354782, d356416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d354782, d356416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d354796 q = 1) (hb : d356430 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d354796, d356430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d354796, d356430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro96838 (p : Pattern) (ha : d354797 p = 1) (hb : d356431 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d354778 q = 1) (hb : d356412 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d354778, d356412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96833 q ha hb
    | true =>
      simp only [d354778, d356412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d354779 q = 1) (hb : d356413 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d354779, d356413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354779, d356413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d354784 q = 1) (hb : d356418 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d354784, d356418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d354784, d356418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d354785 q = 1) (hb : d356419 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d354785, d356419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d354785, d356419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d354786 q = 1) (hb : d356420 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d354786, d356420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d354786, d356420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d354797 q = 1) (hb : d356431 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d354797, d356431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d354797, d356431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro96839 (p : Pattern) (ha : d354803 p = 1) (hb : d356437 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d354788 q = 1) (hb : d356422 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d354788, d356422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96834 q ha hb
    | true =>
      simp only [d354788, d356422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96835 q ha hb
  have h2 (q : Pattern) (ha : d354789 q = 1) (hb : d356423 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d354789, d356423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354789, d356423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d354790 q = 1) (hb : d356424 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d354790, d356424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d354790, d356424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d354791 q = 1) (hb : d356425 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d354791, d356425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354791, d356425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d354792 q = 1) (hb : d356426 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d354792, d356426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354792, d356426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d354798 q = 1) (hb : d356432 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d354798, d356432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96837 q ha hb
    | true =>
      simp only [d354798, d356432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96838 q ha hb
  have h7 (q : Pattern) (ha : d354799 q = 1) (hb : d356433 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d354799, d356433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354799, d356433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d354800 q = 1) (hb : d356434 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d354800, d356434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d354800, d356434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d354801 q = 1) (hb : d356435 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d354801, d356435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354801, d356435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d354802 q = 1) (hb : d356436 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d354802, d356436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354802, d356436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d354803 q = 1) (hb : d356437 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d354803, d356437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d354803, d356437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro96840 (p : Pattern) (ha : d354808 p = 1) (hb : d356442 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d354774 q = 1) (hb : d356408 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d354774, d356408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96832 q ha hb
    | true =>
      simp only [d354774, d356408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d354775 q = 1) (hb : d356409 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d354775, d356409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354775, d356409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d354778 q = 1) (hb : d356412 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d354778, d356412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96833 q ha hb
    | true =>
      simp only [d354778, d356412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d354779 q = 1) (hb : d356413 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d354779, d356413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354779, d356413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d354780 q = 1) (hb : d356414 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d354780, d356414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d354780, d356414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d354781 q = 1) (hb : d356415 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d354781, d356415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d354781, d356415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d354807 q = 1) (hb : d356441 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d354807, d356441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354807, d356441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d354808 q = 1) (hb : d356442 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d354808, d356442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354808, d356442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro96841 (p : Pattern) (ha : d354810 p = 1) (hb : d356444 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d354778 q = 1) (hb : d356412 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d354778, d356412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96833 q ha hb
    | true =>
      simp only [d354778, d356412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d354779 q = 1) (hb : d356413 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d354779, d356413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354779, d356413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d354784 q = 1) (hb : d356418 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d354784, d356418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d354784, d356418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d354785 q = 1) (hb : d356419 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d354785, d356419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d354785, d356419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d354809 q = 1) (hb : d356443 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d354809, d356443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354809, d356443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d354810 q = 1) (hb : d356444 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d354810, d356444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354810, d356444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro96842 (p : Pattern) (ha : d354817 p = 1) (hb : d356451 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d354774 q = 1) (hb : d356408 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d354774, d356408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96832 q ha hb
    | true =>
      simp only [d354774, d356408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d354775 q = 1) (hb : d356409 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d354775, d356409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354775, d356409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d354778 q = 1) (hb : d356412 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d354778, d356412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96833 q ha hb
    | true =>
      simp only [d354778, d356412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d354779 q = 1) (hb : d356413 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d354779, d356413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354779, d356413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d354780 q = 1) (hb : d356414 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d354780, d356414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d354780, d356414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d354815 q = 1) (hb : d356449 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d354815, d356449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354815, d356449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d354816 q = 1) (hb : d356450 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d354816, d356450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d354816, d356450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d354817 q = 1) (hb : d356451 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d354817, d356451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354817, d356451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro96843 (p : Pattern) (ha : d354820 p = 1) (hb : d356454 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d354778 q = 1) (hb : d356412 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d354778, d356412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96833 q ha hb
    | true =>
      simp only [d354778, d356412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d354779 q = 1) (hb : d356413 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d354779, d356413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354779, d356413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d354784 q = 1) (hb : d356418 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d354784, d356418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d354784, d356418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d354818 q = 1) (hb : d356452 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d354818, d356452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354818, d356452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d354819 q = 1) (hb : d356453 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d354819, d356453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d354819, d356453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d354820 q = 1) (hb : d356454 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d354820, d356454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354820, d356454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro96844 (p : Pattern) (ha : d354834 p = 1) (hb : d356461 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d354563 q = 1) (hb : d356202 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d354563, d356202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96794 q ha hb
    | true =>
      simp only [d354563, d356202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d354564 q = 1) (hb : d356203 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d354564, d356203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d354564, d356203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d354824 q = 1) (hb : d356458 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d354824, d356458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354824, d356458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d354828 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d354829 q = 1) (hb : d356459 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d354829, d356459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d354829, d356459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d354830 q = 1) (hb : d356460 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d354830, d356460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d354830, d356460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d354375 q = 1) (hb : d356011 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d354375, d356011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96758 q ha hb
    | true =>
      simp only [d354375, d356011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d354376 q = 1) (hb : d356012 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d354376, d356012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d354376, d356012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d354565 q = 1) (hb : d356204 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d354565, d356204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d354565, d356204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d354831 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d354832 q = 1) (hb : d356205 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d354832, d356205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d354832, d356205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d354833 q = 1) (hb : d356206 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d354833, d356206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d354833, d356206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d354834 q = 1) (hb : d356461 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d354834, d356461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d354834, d356461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro96845 (p : Pattern) (ha : d354840 p = 1) (hb : d356010 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d354371 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d44880 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d46864 q = 1) (hb : d253268 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d46864, d253268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d46864, d253268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d276820 q = 1) (hb : d354372 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d276820, d354372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d276820, d354372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d354373 q = 1) (hb : d356009 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d354373, d356009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354373, d356009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d46865 q = 1) (hb : d354133 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d46865, d354133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46865, d354133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d354839 q = 1) (hb : d355884 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d354839, d355884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d354839, d355884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d354840 q = 1) (hb : d356010 q = 1) : d0 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d354840, d356010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d354840, d356010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro96846 (p : Pattern) (ha : d354846 p = 1) (hb : d356466 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d354563 q = 1) (hb : d356202 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d354563, d356202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96794 q ha hb
    | true =>
      simp only [d354563, d356202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d354564 q = 1) (hb : d356203 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d354564, d356203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d354564, d356203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d354375 q = 1) (hb : d356011 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d354375, d356011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96758 q ha hb
    | true =>
      simp only [d354375, d356011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d354376 q = 1) (hb : d356012 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d354376, d356012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d354376, d356012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d354565 q = 1) (hb : d356204 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d354565, d356204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d354565, d356204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d354572 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d354573 q = 1) (hb : d356205 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d354573, d356205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d354573, d356205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d354574 q = 1) (hb : d356206 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d354574, d356206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d354574, d356206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d354841 q = 1) (hb : d356011 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d354841, d356011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96845 q ha hb
    | true =>
      simp only [d354841, d356011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d354842 q = 1) (hb : d356012 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d354842, d356012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d354842, d356012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d354248 q = 1) (hb : d355886 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d354248, d355886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96735 q ha hb
    | true =>
      simp only [d354248, d355886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d354249 q = 1) (hb : d355887 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d354249, d355887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d354249, d355887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d354843 q = 1) (hb : d356013 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d354843, d356013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d354843, d356013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d354844 q = 1) (hb : d356221 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d354844, d356221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d354844, d356221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d354845 q = 1) (hb : d356222 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d354845, d356222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d354845, d356222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d354846 q = 1) (hb : d356466 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d354846, d356466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d354846, d356466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro96847 (p : Pattern) (ha : d354855 p = 1) (hb : d356466 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d354563 q = 1) (hb : d356202 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d354563, d356202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96794 q ha hb
    | true =>
      simp only [d354563, d356202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d354564 q = 1) (hb : d356203 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d354564, d356203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d354564, d356203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d354841 q = 1) (hb : d356011 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d354841, d356011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96845 q ha hb
    | true =>
      simp only [d354841, d356011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d354842 q = 1) (hb : d356012 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d354842, d356012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d354842, d356012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d354852 q = 1) (hb : d356204 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d354852, d356204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d354852, d356204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d354853 q = 1) (hb : d356205 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d354853, d356205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d354853, d356205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d354854 q = 1) (hb : d356206 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d354854, d356206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d354854, d356206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d354248 q = 1) (hb : d355886 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d354248, d355886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96735 q ha hb
    | true =>
      simp only [d354248, d355886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d354249 q = 1) (hb : d355887 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d354249, d355887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d354249, d355887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d354843 q = 1) (hb : d356013 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d354843, d356013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d354843, d356013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d354844 q = 1) (hb : d356221 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d354844, d356221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d354844, d356221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d354845 q = 1) (hb : d356222 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d354845, d356222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d354845, d356222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d354855 q = 1) (hb : d356466 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d354855, d356466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d354855, d356466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro96848 (p : Pattern) (ha : d354861 p = 1) (hb : d356473 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d354835 q = 1) (hb : d356462 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d354835, d356462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96844 q ha hb
    | true =>
      simp only [d354835, d356462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d354836 q = 1) (hb : d356463 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d354836, d356463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d354836, d356463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d354837 q = 1) (hb : d356464 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d354837, d356464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354837, d356464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d354838 q = 1) (hb : d356465 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d354838, d356465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d354838, d356465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d354847 q = 1) (hb : d356467 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d354847, d356467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96846 q ha hb
    | true =>
      simp only [d354847, d356467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d354848 q = 1) (hb : d356468 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d354848, d356468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d354848, d356468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d354849 q = 1) (hb : d356469 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d354849, d356469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354849, d356469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d354850 q = 1) (hb : d356470 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d354850, d356470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d354850, d356470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d354851 q = 1) (hb : d356471 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d354851, d356471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d354851, d356471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d354856 q = 1) (hb : d356467 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d354856, d356467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96847 q ha hb
    | true =>
      simp only [d354856, d356467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d354857 q = 1) (hb : d356468 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d354857, d356468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d354857, d356468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d354858 q = 1) (hb : d356469 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d354858, d356469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354858, d356469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d354859 q = 1) (hb : d356470 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d354859, d356470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d354859, d356470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d354589 q = 1) (hb : d356224 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d354589, d356224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96797 q ha hb
    | true =>
      simp only [d354589, d356224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d354590 q = 1) (hb : d356225 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d354590, d356225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d354590, d356225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d354591 q = 1) (hb : d356226 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d354591, d356226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354591, d356226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d354592 q = 1) (hb : d356227 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d354592, d356227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d354592, d356227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d354860 q = 1) (hb : d356472 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d354860, d356472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d354860, d356472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d354861 q = 1) (hb : d356473 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d354861, d356473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d354861, d356473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro96849 (p : Pattern) (ha : d354865 p = 1) (hb : d356477 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d354589 q = 1) (hb : d356224 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d354589, d356224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96797 q ha hb
    | true =>
      simp only [d354589, d356224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d354590 q = 1) (hb : d356225 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d354590, d356225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d354590, d356225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d354591 q = 1) (hb : d356226 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d354591, d356226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354591, d356226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d354592 q = 1) (hb : d356227 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d354592, d356227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d354592, d356227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d354754 q = 1) (hb : d356388 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d354754, d356388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96828 q ha hb
    | true =>
      simp only [d354754, d356388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d354755 q = 1) (hb : d356389 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d354755, d356389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d354755, d356389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d354756 q = 1) (hb : d356390 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d354756, d356390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354756, d356390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d354757 q = 1) (hb : d356391 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d354757, d356391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d354757, d356391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d354758 q = 1) (hb : d356392 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d354758, d356392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d354758, d356392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d354761 q = 1) (hb : d356395 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d354761, d356395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d354761, d356395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d354865 q = 1) (hb : d356477 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d354865, d356477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d354865, d356477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro96850 (p : Pattern) (ha : d354871 p = 1) (hb : d356483 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d354862 q = 1) (hb : d356474 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d354862, d356474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96848 q ha hb
    | true =>
      simp only [d354862, d356474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96829 q ha hb
  have h2 (q : Pattern) (ha : d354863 q = 1) (hb : d356475 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d354863, d356475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354863, d356475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d354864 q = 1) (hb : d356476 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d354864, d356476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354864, d356476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d354866 q = 1) (hb : d356478 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d354866, d356478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96829 q ha hb
    | true =>
      simp only [d354866, d356478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96849 q ha hb
  have h5 (q : Pattern) (ha : d354867 q = 1) (hb : d356479 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d354867, d356479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354867, d356479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d354868 q = 1) (hb : d356480 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d354868, d356480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354868, d356480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d354869 q = 1) (hb : d356481 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d354869, d356481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d354869, d356481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d354763 q = 1) (hb : d356397 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d354763, d356397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96829 q ha hb
    | true =>
      simp only [d354763, d356397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96830 q ha hb
  have h9 (q : Pattern) (ha : d354764 q = 1) (hb : d356398 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d354764, d356398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354764, d356398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d354765 q = 1) (hb : d356399 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d354765, d356399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354765, d356399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d354767 q = 1) (hb : d356401 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d354767, d356401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96830 q ha hb
    | true =>
      simp only [d354767, d356401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96831 q ha hb
  have h12 (q : Pattern) (ha : d354768 q = 1) (hb : d356402 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d354768, d356402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354768, d356402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d354769 q = 1) (hb : d356403 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d354769, d356403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354769, d356403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d354770 q = 1) (hb : d356404 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d354770, d356404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d354770, d356404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d354870 q = 1) (hb : d356482 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d354870, d356482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d354870, d356482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d354871 q = 1) (hb : d356483 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d354871, d356483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d354871, d356483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h16 p ha hb
theorem andIntro96851 (p : Pattern) (ha : d354877 p = 1) (hb : d356489 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d354872 q = 1) (hb : d356484 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d354872, d356484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96850 q ha hb
    | true =>
      simp only [d354872, d356484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d354873 q = 1) (hb : d356485 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d354873, d356485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354873, d356485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d354774 q = 1) (hb : d356408 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d354774, d356408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96832 q ha hb
    | true =>
      simp only [d354774, d356408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d354775 q = 1) (hb : d356409 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d354775, d356409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354775, d356409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d354874 q = 1) (hb : d356486 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d354874, d356486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d354874, d356486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d354875 q = 1) (hb : d356487 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d354875, d356487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d354875, d356487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d354876 q = 1) (hb : d356488 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d354876, d356488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d354876, d356488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d354877 q = 1) (hb : d356489 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d354877, d356489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354877, d356489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro96852 (p : Pattern) (ha : d354883 p = 1) (hb : d356495 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d354774 q = 1) (hb : d356408 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d354774, d356408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96832 q ha hb
    | true =>
      simp only [d354774, d356408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d354775 q = 1) (hb : d356409 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d354775, d356409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354775, d356409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d354880 q = 1) (hb : d356492 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d354880, d356492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d354880, d356492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d354881 q = 1) (hb : d356493 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d354881, d356493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d354881, d356493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d354882 q = 1) (hb : d356494 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d354882, d356494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d354882, d356494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d354883 q = 1) (hb : d356495 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d354883, d356495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354883, d356495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro96853 (p : Pattern) (ha : d354889 p = 1) (hb : d356501 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d354811 q = 1) (hb : d356445 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d354811, d356445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96840 q ha hb
    | true =>
      simp only [d354811, d356445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96841 q ha hb
  have h2 (q : Pattern) (ha : d354812 q = 1) (hb : d356446 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d354812, d356446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354812, d356446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d354813 q = 1) (hb : d356447 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d354813, d356447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d354813, d356447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d354814 q = 1) (hb : d356448 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d354814, d356448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354814, d356448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d354821 q = 1) (hb : d356455 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d354821, d356455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96842 q ha hb
    | true =>
      simp only [d354821, d356455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96843 q ha hb
  have h6 (q : Pattern) (ha : d354822 q = 1) (hb : d356456 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d354822, d356456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354822, d356456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d354823 q = 1) (hb : d356457 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d354823, d356457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d354823, d356457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d354878 q = 1) (hb : d356490 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d354878, d356490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96851 q ha hb
    | true =>
      simp only [d354878, d356490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96834 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d354788 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d354879 q = 1) (hb : d356491 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d354879, d356491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d354879, d356491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d354884 q = 1) (hb : d356496 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d354884, d356496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96852 q ha hb
    | true =>
      simp only [d354884, d356496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d354885 q = 1) (hb : d356497 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d354885, d356497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d354885, d356497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d354886 q = 1) (hb : d356498 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d354886, d356498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d354886, d356498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d354887 q = 1) (hb : d356499 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d354887, d356499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d354887, d356499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d354888 q = 1) (hb : d356500 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d354888, d356500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d354888, d356500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d354889 q = 1) (hb : d356501 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d354889, d356501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354889, d356501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro96854 (p : Pattern) (ha : d354890 p = 1) (hb : d356502 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d354774 q = 1) (hb : d356408 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d354774, d356408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96832 q ha hb
    | true =>
      simp only [d354774, d356408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d354775 q = 1) (hb : d356409 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d354775, d356409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354775, d356409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d354778 q = 1) (hb : d356412 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d354778, d356412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96833 q ha hb
    | true =>
      simp only [d354778, d356412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d354779 q = 1) (hb : d356413 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d354779, d356413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354779, d356413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d354780 q = 1) (hb : d356414 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d354780, d356414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d354780, d356414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d354781 q = 1) (hb : d356415 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d354781, d356415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d354781, d356415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d354807 q = 1) (hb : d356441 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d354807, d356441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354807, d356441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d354890 q = 1) (hb : d356502 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d354890, d356502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d354890, d356502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro96855 (p : Pattern) (ha : d354891 p = 1) (hb : d356503 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d354778 q = 1) (hb : d356412 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d354778, d356412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96833 q ha hb
    | true =>
      simp only [d354778, d356412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d354779 q = 1) (hb : d356413 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d354779, d356413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354779, d356413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d354784 q = 1) (hb : d356418 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d354784, d356418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d354784, d356418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d354785 q = 1) (hb : d356419 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d354785, d356419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d354785, d356419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d354809 q = 1) (hb : d356443 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d354809, d356443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354809, d356443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d354891 q = 1) (hb : d356503 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d354891, d356503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d354891, d356503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro96856 (p : Pattern) (ha : d354896 p = 1) (hb : d356508 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d354774 q = 1) (hb : d356408 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d354774, d356408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96832 q ha hb
    | true =>
      simp only [d354774, d356408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d354775 q = 1) (hb : d356409 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d354775, d356409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354775, d356409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d354778 q = 1) (hb : d356412 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d354778, d356412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96833 q ha hb
    | true =>
      simp only [d354778, d356412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d354779 q = 1) (hb : d356413 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d354779, d356413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354779, d356413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d354780 q = 1) (hb : d356414 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d354780, d356414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d354780, d356414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d354815 q = 1) (hb : d356449 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d354815, d356449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354815, d356449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d354816 q = 1) (hb : d356450 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d354816, d356450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d354816, d356450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d354896 q = 1) (hb : d356508 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d354896, d356508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d354896, d356508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro96857 (p : Pattern) (ha : d354897 p = 1) (hb : d356509 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d354778 q = 1) (hb : d356412 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d354778, d356412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96833 q ha hb
    | true =>
      simp only [d354778, d356412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d354779 q = 1) (hb : d356413 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d354779, d356413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354779, d356413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d354784 q = 1) (hb : d356418 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d354784, d356418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d354784, d356418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d354818 q = 1) (hb : d356452 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d354818, d356452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354818, d356452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d354819 q = 1) (hb : d356453 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d354819, d356453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d354819, d356453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d354897 q = 1) (hb : d356509 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d354897, d356509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d354897, d356509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro96858 (p : Pattern) (ha : d354901 p = 1) (hb : d356513 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d354872 q = 1) (hb : d356484 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d354872, d356484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96850 q ha hb
    | true =>
      simp only [d354872, d356484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d354873 q = 1) (hb : d356485 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d354873, d356485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354873, d356485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d354774 q = 1) (hb : d356408 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d354774, d356408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96832 q ha hb
    | true =>
      simp only [d354774, d356408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d354775 q = 1) (hb : d356409 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d354775, d356409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354775, d356409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d354874 q = 1) (hb : d356486 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d354874, d356486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d354874, d356486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d354875 q = 1) (hb : d356487 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d354875, d356487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d354875, d356487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d354876 q = 1) (hb : d356488 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d354876, d356488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d354876, d356488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d354901 q = 1) (hb : d356513 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d354901, d356513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d354901, d356513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro96859 (p : Pattern) (ha : d354904 p = 1) (hb : d356516 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d354774 q = 1) (hb : d356408 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d354774, d356408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96832 q ha hb
    | true =>
      simp only [d354774, d356408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d354775 q = 1) (hb : d356409 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d354775, d356409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354775, d356409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d354880 q = 1) (hb : d356492 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d354880, d356492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d354880, d356492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d354881 q = 1) (hb : d356493 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d354881, d356493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d354881, d356493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d354882 q = 1) (hb : d356494 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d354882, d356494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d354882, d356494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d354904 q = 1) (hb : d356516 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d354904, d356516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d354904, d356516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro96860 (p : Pattern) (ha : d354910 p = 1) (hb : d356522 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d354811 q = 1) (hb : d356445 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d354811, d356445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96840 q ha hb
    | true =>
      simp only [d354811, d356445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96841 q ha hb
  have h2 (q : Pattern) (ha : d354812 q = 1) (hb : d356446 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d354812, d356446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354812, d356446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d354813 q = 1) (hb : d356447 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d354813, d356447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d354813, d356447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d354814 q = 1) (hb : d356448 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d354814, d356448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354814, d356448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d354821 q = 1) (hb : d356455 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d354821, d356455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96842 q ha hb
    | true =>
      simp only [d354821, d356455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96843 q ha hb
  have h6 (q : Pattern) (ha : d354822 q = 1) (hb : d356456 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d354822, d356456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354822, d356456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d354823 q = 1) (hb : d356457 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d354823, d356457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d354823, d356457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d354878 q = 1) (hb : d356490 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d354878, d356490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96851 q ha hb
    | true =>
      simp only [d354878, d356490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96834 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d354788 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d354879 q = 1) (hb : d356491 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d354879, d356491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d354879, d356491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d354884 q = 1) (hb : d356496 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d354884, d356496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96852 q ha hb
    | true =>
      simp only [d354884, d356496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d354885 q = 1) (hb : d356497 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d354885, d356497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d354885, d356497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d354886 q = 1) (hb : d356498 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d354886, d356498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d354886, d356498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d354887 q = 1) (hb : d356499 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d354887, d356499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d354887, d356499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d354888 q = 1) (hb : d356500 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d354888, d356500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d354888, d356500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d354892 q = 1) (hb : d356504 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d354892, d356504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96854 q ha hb
    | true =>
      simp only [d354892, d356504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96855 q ha hb
  have h17 (q : Pattern) (ha : d354893 q = 1) (hb : d356505 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d354893, d356505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354893, d356505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d354894 q = 1) (hb : d356506 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d354894, d356506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d354894, d356506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d354895 q = 1) (hb : d356507 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d354895, d356507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354895, d356507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d354898 q = 1) (hb : d356510 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d354898, d356510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96856 q ha hb
    | true =>
      simp only [d354898, d356510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96857 q ha hb
  have h21 (q : Pattern) (ha : d354899 q = 1) (hb : d356511 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d354899, d356511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354899, d356511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d354900 q = 1) (hb : d356512 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d354900, d356512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d354900, d356512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d354902 q = 1) (hb : d356514 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d354902, d356514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96858 q ha hb
    | true =>
      simp only [d354902, d356514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96837 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d354798 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d354903 q = 1) (hb : d356515 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d354903, d356515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d354903, d356515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d354905 q = 1) (hb : d356517 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d354905, d356517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96859 q ha hb
    | true =>
      simp only [d354905, d356517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d354906 q = 1) (hb : d356518 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d354906, d356518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d354906, d356518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d354907 q = 1) (hb : d356519 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d354907, d356519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d354907, d356519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d354908 q = 1) (hb : d356520 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d354908, d356520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d354908, d356520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d354909 q = 1) (hb : d356521 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d354909, d356521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d354909, d356521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d354910 q = 1) (hb : d356522 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d354910, d356522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d354910, d356522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro96861 (p : Pattern) (ha : d354917 p = 1) (hb : d356529 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d354788 q = 1) (hb : d356422 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d354788, d356422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96834 q ha hb
    | true =>
      simp only [d354788, d356422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96835 q ha hb
  have h2 (q : Pattern) (ha : d354789 q = 1) (hb : d356423 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d354789, d356423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354789, d356423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d354790 q = 1) (hb : d356424 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d354790, d356424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d354790, d356424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d354791 q = 1) (hb : d356425 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d354791, d356425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354791, d356425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d354792 q = 1) (hb : d356426 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d354792, d356426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354792, d356426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d354912 q = 1) (hb : d356524 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d354912, d356524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96835 q ha hb
    | true =>
      simp only [d354912, d356524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d354913 q = 1) (hb : d356525 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d354913, d356525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354913, d356525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d354914 q = 1) (hb : d356526 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d354914, d356526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d354914, d356526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d354915 q = 1) (hb : d356527 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d354915, d356527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354915, d356527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d354916 q = 1) (hb : d356528 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d354916, d356528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354916, d356528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d354917 q = 1) (hb : d356529 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d354917, d356529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d354917, d356529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro96862 (p : Pattern) (ha : d354923 p = 1) (hb : d356535 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d354912 q = 1) (hb : d356524 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d354912, d356524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96835 q ha hb
    | true =>
      simp only [d354912, d356524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d354913 q = 1) (hb : d356525 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d354913, d356525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354913, d356525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d354914 q = 1) (hb : d356526 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d354914, d356526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d354914, d356526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d354915 q = 1) (hb : d356527 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d354915, d356527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354915, d356527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d354916 q = 1) (hb : d356528 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d354916, d356528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354916, d356528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d354918 q = 1) (hb : d356530 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d354918, d356530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96838 q ha hb
    | true =>
      simp only [d354918, d356530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d354919 q = 1) (hb : d356531 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d354919, d356531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354919, d356531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d354920 q = 1) (hb : d356532 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d354920, d356532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d354920, d356532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d354921 q = 1) (hb : d356533 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d354921, d356533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354921, d356533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d354922 q = 1) (hb : d356534 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d354922, d356534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354922, d356534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d354923 q = 1) (hb : d356535 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d354923, d356535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d354923, d356535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro96863 (p : Pattern) (ha : d354930 p = 1) (hb : d356542 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d354902 q = 1) (hb : d356514 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d354902, d356514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96858 q ha hb
    | true =>
      simp only [d354902, d356514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96837 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d354798 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d354903 q = 1) (hb : d356515 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d354903, d356515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d354903, d356515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d354905 q = 1) (hb : d356517 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d354905, d356517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96859 q ha hb
    | true =>
      simp only [d354905, d356517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d354906 q = 1) (hb : d356518 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d354906, d356518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d354906, d356518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d354907 q = 1) (hb : d356519 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d354907, d356519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d354907, d356519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d354928 q = 1) (hb : d356540 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d354928, d356540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354928, d356540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d354929 q = 1) (hb : d356541 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d354929, d356541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354929, d356541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d354930 q = 1) (hb : d356542 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d354930, d356542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354930, d356542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro96864 (p : Pattern) (ha : d354932 p = 1) (hb : d356544 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d354918 q = 1) (hb : d356530 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d354918, d356530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96838 q ha hb
    | true =>
      simp only [d354918, d356530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d354919 q = 1) (hb : d356531 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d354919, d356531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354919, d356531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d354920 q = 1) (hb : d356532 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d354920, d356532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d354920, d356532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d354921 q = 1) (hb : d356533 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d354921, d356533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354921, d356533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d354922 q = 1) (hb : d356534 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d354922, d356534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354922, d356534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d354932 q = 1) (hb : d356544 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d354932, d356544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354932, d356544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro96865 (p : Pattern) (ha : d354952 p = 1) (hb : d356560 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d354938 q = 1) (hb : d356550 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d354938, d356550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354938, d356550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96844 q ha hb
  have h2 (q : Pattern) (ha : d354835 q = 1) (hb : d356462 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d354835, d356462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96844 q ha hb
    | true =>
      simp only [d354835, d356462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d354939 q = 1) (hb : d356551 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d354939, d356551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d354939, d356551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d354836 q = 1) (hb : d356463 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d354836, d356463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d354836, d356463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d354940 q = 1) (hb : d356552 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d354940, d356552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d354940, d356552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d354941 q = 1) (hb : d356553 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d354941, d356553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d354941, d356553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d354942 q = 1) (hb : d356554 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d354942, d356554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354942, d356554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96846 q ha hb
  have h8 (q : Pattern) (ha : d354847 q = 1) (hb : d356467 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d354847, d356467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96846 q ha hb
    | true =>
      simp only [d354847, d356467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d354943 q = 1) (hb : d356555 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d354943, d356555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d354943, d356555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d354848 q = 1) (hb : d356468 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d354848, d356468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d354848, d356468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d354944 q = 1) (hb : d356556 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d354944, d356556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d354944, d356556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d354945 q = 1) (hb : d356557 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d354945, d356557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d354945, d356557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d354946 q = 1) (hb : d356558 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d354946, d356558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d354946, d356558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d354947 q = 1) (hb : d356554 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d354947, d356554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354947, d356554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96847 q ha hb
  have h15 (q : Pattern) (ha : d354856 q = 1) (hb : d356467 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d354856, d356467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96847 q ha hb
    | true =>
      simp only [d354856, d356467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d354948 q = 1) (hb : d356555 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d354948, d356555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d354948, d356555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d354857 q = 1) (hb : d356468 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d354857, d356468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d354857, d356468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d354949 q = 1) (hb : d356556 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d354949, d356556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d354949, d356556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d354950 q = 1) (hb : d356557 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d354950, d356557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d354950, d356557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d354680 q = 1) (hb : d356315 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d354680, d356315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354680, d356315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96797 q ha hb
  have h21 (q : Pattern) (ha : d354589 q = 1) (hb : d356224 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d354589, d356224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96797 q ha hb
    | true =>
      simp only [d354589, d356224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d354681 q = 1) (hb : d356316 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d354681, d356316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d354681, d356316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d354590 q = 1) (hb : d356225 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d354590, d356225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d354590, d356225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d354682 q = 1) (hb : d356317 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d354682, d356317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d354682, d356317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d354683 q = 1) (hb : d356318 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d354683, d356318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d354683, d356318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h26 (q : Pattern) (ha : d354951 q = 1) (hb : d356559 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d354951, d356559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d354951, d356559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d354952 q = 1) (hb : d356560 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d354952, d356560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d354952, d356560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  exact h27 p ha hb
theorem andIntro96866 (p : Pattern) (ha : d354958 p = 1) (hb : d356566 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d354671 q = 1) (hb : d356306 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d354671, d356306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354671, d356306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96795 q ha hb
  have h2 (q : Pattern) (ha : d354576 q = 1) (hb : d356211 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d354576, d356211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96795 q ha hb
    | true =>
      simp only [d354576, d356211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d354672 q = 1) (hb : d356307 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d354672, d356307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d354672, d356307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d354577 q = 1) (hb : d356212 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d354577, d356212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d354577, d356212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d354673 q = 1) (hb : d356308 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d354673, d356308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d354673, d356308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d354674 q = 1) (hb : d356309 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d354674, d356309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d354674, d356309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d354675 q = 1) (hb : d356310 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d354675, d356310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354675, d356310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96796 q ha hb
  have h8 (q : Pattern) (ha : d354581 q = 1) (hb : d356216 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d354581, d356216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96796 q ha hb
    | true =>
      simp only [d354581, d356216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d354676 q = 1) (hb : d356311 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d354676, d356311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d354676, d356311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d354582 q = 1) (hb : d356217 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d354582, d356217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d354582, d356217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d354677 q = 1) (hb : d356312 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d354677, d356312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d354677, d356312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d354678 q = 1) (hb : d356313 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d354678, d356313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d354678, d356313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d354679 q = 1) (hb : d356314 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d354679, d356314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d354679, d356314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d354680 q = 1) (hb : d356315 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d354680, d356315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354680, d356315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96797 q ha hb
  have h15 (q : Pattern) (ha : d354589 q = 1) (hb : d356224 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d354589, d356224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96797 q ha hb
    | true =>
      simp only [d354589, d356224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d354681 q = 1) (hb : d356316 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d354681, d356316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d354681, d356316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d354590 q = 1) (hb : d356225 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d354590, d356225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d354590, d356225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d354682 q = 1) (hb : d356317 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d354682, d356317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d354682, d356317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d354683 q = 1) (hb : d356318 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d354683, d356318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d354683, d356318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d354953 q = 1) (hb : d356561 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d354953, d356561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354953, d356561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96828 q ha hb
  have h21 (q : Pattern) (ha : d354754 q = 1) (hb : d356388 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d354754, d356388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96828 q ha hb
    | true =>
      simp only [d354754, d356388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d354954 q = 1) (hb : d356562 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d354954, d356562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d354954, d356562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d354755 q = 1) (hb : d356389 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d354755, d356389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d354755, d356389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d354955 q = 1) (hb : d356563 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d354955, d356563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d354955, d356563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d354956 q = 1) (hb : d356564 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d354956, d356564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d354956, d356564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h26 (q : Pattern) (ha : d354957 q = 1) (hb : d356565 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d354957, d356565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d354957, d356565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d354958 q = 1) (hb : d356566 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d354958, d356566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d354958, d356566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  exact h27 p ha hb
theorem andIntro96867 (p : Pattern) (ha : d354963 p = 1) (hb : d356571 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d354680 q = 1) (hb : d356315 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d354680, d356315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354680, d356315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96797 q ha hb
  have h2 (q : Pattern) (ha : d354589 q = 1) (hb : d356224 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d354589, d356224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96797 q ha hb
    | true =>
      simp only [d354589, d356224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d354681 q = 1) (hb : d356316 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d354681, d356316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d354681, d356316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d354590 q = 1) (hb : d356225 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d354590, d356225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d354590, d356225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d354682 q = 1) (hb : d356317 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d354682, d356317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d354682, d356317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d354683 q = 1) (hb : d356318 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d354683, d356318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d354683, d356318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d354953 q = 1) (hb : d356561 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d354953, d356561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354953, d356561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96828 q ha hb
  have h8 (q : Pattern) (ha : d354754 q = 1) (hb : d356388 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d354754, d356388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96828 q ha hb
    | true =>
      simp only [d354754, d356388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d354954 q = 1) (hb : d356562 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d354954, d356562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d354954, d356562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d354755 q = 1) (hb : d356389 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d354755, d356389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d354755, d356389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d354955 q = 1) (hb : d356563 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d354955, d356563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d354955, d356563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d354956 q = 1) (hb : d356564 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d354956, d356564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d354956, d356564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d354957 q = 1) (hb : d356565 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d354957, d356565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d354957, d356565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d354962 q = 1) (hb : d356570 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d354962, d356570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d354962, d356570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d354963 q = 1) (hb : d356571 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d354963, d356571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d354963, d356571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro96868 (p : Pattern) (ha : d354969 p = 1) (hb : d356577 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d354454 q = 1) (hb : d356094 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d354454, d356094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354454, d356094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96759 q ha hb
  have h2 (q : Pattern) (ha : d354381 q = 1) (hb : d356021 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d354381, d356021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96759 q ha hb
    | true =>
      simp only [d354381, d356021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d354455 q = 1) (hb : d356095 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d354455, d356095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d354455, d356095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d354382 q = 1) (hb : d356022 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d354382, d356022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d354382, d356022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d354456 q = 1) (hb : d356096 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d354456, d356096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d354456, d356096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d354457 q = 1) (hb : d356097 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d354457, d356097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d354457, d356097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d354953 q = 1) (hb : d356561 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d354953, d356561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354953, d356561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96828 q ha hb
  have h8 (q : Pattern) (ha : d354754 q = 1) (hb : d356388 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d354754, d356388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96828 q ha hb
    | true =>
      simp only [d354754, d356388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d354954 q = 1) (hb : d356562 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d354954, d356562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d354954, d356562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d354755 q = 1) (hb : d356389 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d354755, d356389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d354755, d356389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d354955 q = 1) (hb : d356563 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d354955, d356563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d354955, d356563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d354956 q = 1) (hb : d356564 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d354956, d356564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d354956, d356564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d354968 q = 1) (hb : d356576 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d354968, d356576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d354968, d356576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d354962 q = 1) (hb : d356570 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d354962, d356570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d354962, d356570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d354969 q = 1) (hb : d356577 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d354969, d356577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d354969, d356577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro96869 (p : Pattern) (ha : d354973 p = 1) (hb : d356581 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d354953 q = 1) (hb : d356561 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d354953, d356561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354953, d356561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96828 q ha hb
  have h2 (q : Pattern) (ha : d354754 q = 1) (hb : d356388 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d354754, d356388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96828 q ha hb
    | true =>
      simp only [d354754, d356388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d354954 q = 1) (hb : d356562 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d354954, d356562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d354954, d356562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d354755 q = 1) (hb : d356389 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d354755, d356389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d354755, d356389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d354955 q = 1) (hb : d356563 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d354955, d356563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d354955, d356563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d354956 q = 1) (hb : d356564 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d354956, d356564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d354956, d356564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d354962 q = 1) (hb : d356570 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d354962, d356570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d354962, d356570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d354973 q = 1) (hb : d356581 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d354973, d356581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d354973, d356581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro96870 (p : Pattern) (ha : d354979 p = 1) (hb : d356587 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d354959 q = 1) (hb : d356567 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d354959, d356567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96865 q ha hb
    | true =>
      simp only [d354959, d356567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96866 q ha hb
  have h2 (q : Pattern) (ha : d354960 q = 1) (hb : d356568 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d354960, d356568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354960, d356568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d354961 q = 1) (hb : d356569 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d354961, d356569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354961, d356569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d354964 q = 1) (hb : d356572 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d354964, d356572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96866 q ha hb
    | true =>
      simp only [d354964, d356572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96867 q ha hb
  have h5 (q : Pattern) (ha : d354965 q = 1) (hb : d356573 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d354965, d356573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354965, d356573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d354966 q = 1) (hb : d356574 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d354966, d356574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354966, d356574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d354967 q = 1) (hb : d356575 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d354967, d356575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d354967, d356575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d354970 q = 1) (hb : d356578 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d354970, d356578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96866 q ha hb
    | true =>
      simp only [d354970, d356578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96868 q ha hb
  have h9 (q : Pattern) (ha : d354971 q = 1) (hb : d356579 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d354971, d356579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354971, d356579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d354972 q = 1) (hb : d356580 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d354972, d356580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354972, d356580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d354974 q = 1) (hb : d356582 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d354974, d356582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96868 q ha hb
    | true =>
      simp only [d354974, d356582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96869 q ha hb
  have h12 (q : Pattern) (ha : d354975 q = 1) (hb : d356583 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d354975, d356583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354975, d356583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d354976 q = 1) (hb : d356584 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d354976, d356584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354976, d356584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d354977 q = 1) (hb : d356585 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d354977, d356585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d354977, d356585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d354978 q = 1) (hb : d356586 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d354978, d356586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d354978, d356586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d354979 q = 1) (hb : d356587 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d354979, d356587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d354979, d356587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h16 p ha hb
theorem andIntro96871 (p : Pattern) (ha : d354984 p = 1) (hb : d356592 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d354970 q = 1) (hb : d356578 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d354970, d356578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96866 q ha hb
    | true =>
      simp only [d354970, d356578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96868 q ha hb
  have h2 (q : Pattern) (ha : d354971 q = 1) (hb : d356579 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d354971, d356579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354971, d356579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d354972 q = 1) (hb : d356580 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d354972, d356580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354972, d356580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d354974 q = 1) (hb : d356582 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d354974, d356582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96868 q ha hb
    | true =>
      simp only [d354974, d356582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96869 q ha hb
  have h5 (q : Pattern) (ha : d354975 q = 1) (hb : d356583 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d354975, d356583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354975, d356583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d354976 q = 1) (hb : d356584 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d354976, d356584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354976, d356584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d354977 q = 1) (hb : d356585 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d354977, d356585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d354977, d356585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d354982 q = 1) (hb : d356590 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d354982, d356590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d354982, d356590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d354983 q = 1) (hb : d356591 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d354983, d356591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d354983, d356591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d354984 q = 1) (hb : d356592 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d354984, d356592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d354984, d356592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro96872 (p : Pattern) (ha : d354990 p = 1) (hb : d356598 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d354980 q = 1) (hb : d356588 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d354980, d356588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96870 q ha hb
    | true =>
      simp only [d354980, d356588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d354981 q = 1) (hb : d356589 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d354981, d356589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354981, d356589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d354985 q = 1) (hb : d356593 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d354985, d356593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96871 q ha hb
    | true =>
      simp only [d354985, d356593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d354986 q = 1) (hb : d356594 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d354986, d356594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354986, d356594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d354987 q = 1) (hb : d356595 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d354987, d356595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d354987, d356595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d354988 q = 1) (hb : d356596 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d354988, d356596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d354988, d356596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d354989 q = 1) (hb : d356597 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d354989, d356597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d354989, d356597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d354990 q = 1) (hb : d356598 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d354990, d356598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d354990, d356598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro96873 (p : Pattern) (ha : d354992 p = 1) (hb : d356600 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d354974 q = 1) (hb : d356582 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d354974, d356582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96868 q ha hb
    | true =>
      simp only [d354974, d356582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96869 q ha hb
  have h2 (q : Pattern) (ha : d354975 q = 1) (hb : d356583 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d354975, d356583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354975, d356583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d354976 q = 1) (hb : d356584 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d354976, d356584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354976, d356584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d354982 q = 1) (hb : d356590 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d354982, d356590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d354982, d356590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d354991 q = 1) (hb : d356599 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d354991, d356599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d354991, d356599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d354992 q = 1) (hb : d356600 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d354992, d356600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d354992, d356600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro96874 (p : Pattern) (ha : d354998 p = 1) (hb : d356606 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d354985 q = 1) (hb : d356593 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d354985, d356593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96871 q ha hb
    | true =>
      simp only [d354985, d356593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d354986 q = 1) (hb : d356594 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d354986, d356594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354986, d356594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d354993 q = 1) (hb : d356601 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d354993, d356601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96873 q ha hb
    | true =>
      simp only [d354993, d356601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d354994 q = 1) (hb : d356602 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d354994, d356602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354994, d356602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d354995 q = 1) (hb : d356603 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d354995, d356603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d354995, d356603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d354996 q = 1) (hb : d356604 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d354996, d356604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d354996, d356604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d354997 q = 1) (hb : d356605 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d354997, d356605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d354997, d356605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d354998 q = 1) (hb : d356606 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d354998, d356606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d354998, d356606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro96875 (p : Pattern) (ha : d355009 p = 1) (hb : d356612 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d354985 q = 1) (hb : d356593 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d354985, d356593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96871 q ha hb
    | true =>
      simp only [d354985, d356593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d354986 q = 1) (hb : d356594 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d354986, d356594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354986, d356594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d355006 q = 1) (hb : d356609 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d355006, d356609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d355006, d356609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d355007 q = 1) (hb : d356610 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d355007, d356610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d355007, d356610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d355008 q = 1) (hb : d356611 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d355008, d356611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d355008, d356611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d355009 q = 1) (hb : d356612 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d355009, d356612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d355009, d356612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro96876 (p : Pattern) (ha : d355015 p = 1) (hb : d356618 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d354999 q = 1) (hb : d356607 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d354999, d356607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96872 q ha hb
    | true =>
      simp only [d354999, d356607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96874 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d355004 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d355005 q = 1) (hb : d356608 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d355005, d356608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d355005, d356608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d355010 q = 1) (hb : d356613 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d355010, d356613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96875 q ha hb
    | true =>
      simp only [d355010, d356613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d355011 q = 1) (hb : d356614 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d355011, d356614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d355011, d356614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d355012 q = 1) (hb : d356615 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d355012, d356615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d355012, d356615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d355013 q = 1) (hb : d356616 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d355013, d356616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d355013, d356616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d355014 q = 1) (hb : d356617 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d355014, d356617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d355014, d356617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d355015 q = 1) (hb : d356618 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d355015, d356618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d355015, d356618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro96877 (p : Pattern) (ha : d355003 p = 1) (hb : d356623 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d354993 q = 1) (hb : d356601 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d354993, d356601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96873 q ha hb
    | true =>
      simp only [d354993, d356601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d354994 q = 1) (hb : d356602 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d354994, d356602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354994, d356602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d355000 q = 1) (hb : d356620 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d355000, d356620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d355000, d356620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d355001 q = 1) (hb : d356621 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d355001, d356621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d355001, d356621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d355002 q = 1) (hb : d356622 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d355002, d356622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d355002, d356622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d355003 q = 1) (hb : d356623 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d355003, d356623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d355003, d356623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro96878 (p : Pattern) (ha : d355022 p = 1) (hb : d356629 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d355017 q = 1) (hb : d356624 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d355017, d356624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96877 q ha hb
    | true =>
      simp only [d355017, d356624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d355018 q = 1) (hb : d356625 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d355018, d356625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d355018, d356625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d355019 q = 1) (hb : d356626 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d355019, d356626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d355019, d356626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d355020 q = 1) (hb : d356627 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d355020, d356627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d355020, d356627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d355021 q = 1) (hb : d356628 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d355021, d356628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d355021, d356628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d355022 q = 1) (hb : d356629 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d355022, d356629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d355022, d356629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro96879 (p : Pattern) (ha : d355028 p = 1) (hb : d356635 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d354794 q = 1) (hb : d356428 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d354794, d356428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354794, d356428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96836 q ha hb
  have h2 (q : Pattern) (ha : d354795 q = 1) (hb : d356429 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d354795, d356429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d354795, d356429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d354804 q = 1) (hb : d356438 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d354804, d356438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96836 q ha hb
    | true =>
      simp only [d354804, d356438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96839 q ha hb
  have h4 (q : Pattern) (ha : d354805 q = 1) (hb : d356439 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d354805, d356439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d354805, d356439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d354806 q = 1) (hb : d356440 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d354806, d356440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d354806, d356440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d354911 q = 1) (hb : d356523 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d354911, d356523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96853 q ha hb
    | true =>
      simp only [d354911, d356523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96860 q ha hb
  have h7 (q : Pattern) (ha : d354924 q = 1) (hb : d356536 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d354924, d356536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96861 q ha hb
    | true =>
      simp only [d354924, d356536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96862 q ha hb
  have h8 (q : Pattern) (ha : d354925 q = 1) (hb : d356537 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d354925, d356537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d354925, d356537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d354926 q = 1) (hb : d356538 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d354926, d356538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d354926, d356538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d354927 q = 1) (hb : d356539 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d354927, d356539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d354927, d356539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d354931 q = 1) (hb : d356543 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d354931, d356543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354931, d356543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96863 q ha hb
  have h12 (q : Pattern) (ha : d354933 q = 1) (hb : d356545 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d354933, d356545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354933, d356545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96864 q ha hb
  have h13 (q : Pattern) (ha : d354934 q = 1) (hb : d356546 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d354934, d356546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d354934, d356546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d354935 q = 1) (hb : d356547 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d354935, d356547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d354935, d356547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d354936 q = 1) (hb : d356548 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d354936, d356548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d354936, d356548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d354937 q = 1) (hb : d356549 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d354937, d356549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d354937, d356549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d355016 q = 1) (hb : d356619 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d355016, d356619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d355016, d356619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96876 q ha hb
  have h18 (q : Pattern) (ha : d355023 q = 1) (hb : d356630 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d355023, d356630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d355023, d356630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96878 q ha hb
  have h19 (q : Pattern) (ha : d355024 q = 1) (hb : d356631 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d355024, d356631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d355024, d356631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d355025 q = 1) (hb : d356632 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d355025, d356632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d355025, d356632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d355026 q = 1) (hb : d356633 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d355026, d356633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d355026, d356633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d355027 q = 1) (hb : d356634 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d355027, d356634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d355027, d356634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d355028 q = 1) (hb : d356635 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d355028, d356635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d355028, d356635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro96880 (p : Pattern) (ha : d355034 p = 1) (hb : d356641 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d355029 q = 1) (hb : d356636 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d355029, d356636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d355029, d356636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96879 q ha hb
  have h2 (q : Pattern) (ha : d355030 q = 1) (hb : d356637 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d355030, d356637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d355030, d356637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d355031 q = 1) (hb : d356638 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d355031, d356638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d355031, d356638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d355032 q = 1) (hb : d356639 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d355032, d356639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d355032, d356639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d355033 q = 1) (hb : d356640 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d355033, d356640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d355033, d356640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d355034 q = 1) (hb : d356641 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d355034, d356641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d355034, d356641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro96881 (p : Pattern) (ha : d276849 p = 1) (hb : d355451 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d44880 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d46864 q = 1) (hb : d253268 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d46864, d253268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d46864, d253268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d276820 q = 1) (hb : d354372 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d276820, d354372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d276820, d354372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d276821 q = 1) (hb : d355450 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d276821, d355450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d276821, d355450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d276849 q = 1) (hb : d355451 q = 1) : d0 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d276849, d355451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d276849, d355451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h5 p ha hb
theorem andIntro96882 (p : Pattern) (ha : d355460 p = 1) (hb : d356652 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d355443 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d276850 q = 1) (hb : d355452 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d276850, d355452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d276850, d355452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96881 q ha hb
  have h3 (q : Pattern) (ha : d46868 q = 1) (hb : d355080 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d46868, d355080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d46868, d355080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96717 q ha hb
  have h4 (q : Pattern) (ha : d355453 q = 1) (hb : d356646 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d355453, d356646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d355453, d356646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d355454 q = 1) (hb : d356647 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d355454, d356647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d355454, d356647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h6 (q : Pattern) (ha : d276872 q = 1) (hb : d355455 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d276872, d355455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96881 q ha hb
    | true =>
      simp only [d276872, d355455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d46871 q = 1) (hb : d354136 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d46871, d354136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96717 q ha hb
    | true =>
      simp only [d46871, d354136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d355456 q = 1) (hb : d356648 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d355456, d356648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d355456, d356648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d355457 q = 1) (hb : d356649 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d355457, d356649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d355457, d356649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h10 (q : Pattern) (ha : d355458 q = 1) (hb : d356650 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d355458, d356650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d355458, d356650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d355459 q = 1) (hb : d356651 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d355459, d356651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d355459, d356651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h12 (q : Pattern) (ha : d355460 q = 1) (hb : d356652 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d355460, d356652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d355460, d356652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro96883 (p : Pattern) (ha : d355466 p = 1) (hb : d356658 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d355449 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d355448 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d355461 q = 1) (hb : d356653 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d355461, d356653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96882 q ha hb
    | true =>
      simp only [d355461, d356653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d355462 q = 1) (hb : d356654 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d355462, d356654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d355462, d356654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h5 (q : Pattern) (ha : d355463 q = 1) (hb : d356655 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d355463, d356655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d355463, d356655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d355464 q = 1) (hb : d356656 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d355464, d356656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d355464, d356656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h7 (q : Pattern) (ha : d355465 q = 1) (hb : d356657 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d355465, d356657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d355465, d356657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d355466 q = 1) (hb : d356658 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d355466, d356658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d355466, d356658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro96884 (p : Pattern) (ha : d355468 p = 1) (hb : d356660 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d355448 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d355461 q = 1) (hb : d356653 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d355461, d356653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96882 q ha hb
    | true =>
      simp only [d355461, d356653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d355462 q = 1) (hb : d356654 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d355462, d356654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d355462, d356654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h4 (q : Pattern) (ha : d355463 q = 1) (hb : d356655 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d355463, d356655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d355463, d356655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d355464 q = 1) (hb : d356656 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d355464, d356656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d355464, d356656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h6 (q : Pattern) (ha : d355465 q = 1) (hb : d356657 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d355465, d356657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d355465, d356657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d355467 q = 1) (hb : d356659 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d355467, d356659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d355467, d356659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h8 (q : Pattern) (ha : d355468 q = 1) (hb : d356660 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d355468, d356660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d355468, d356660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro96885 (p : Pattern) (ha : d355472 p = 1) (hb : d356664 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d276850 q = 1) (hb : d355452 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d276850, d355452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d276850, d355452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96881 q ha hb
  have h2 (q : Pattern) (ha : d46868 q = 1) (hb : d355080 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d46868, d355080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46868, d355080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96717 q ha hb
  have h3 (q : Pattern) (ha : d355453 q = 1) (hb : d356646 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d355453, d356646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d355453, d356646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d355454 q = 1) (hb : d356647 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d355454, d356647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d355454, d356647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d276872 q = 1) (hb : d355455 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d276872, d355455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96881 q ha hb
    | true =>
      simp only [d276872, d355455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d46871 q = 1) (hb : d354136 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d46871, d354136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96717 q ha hb
    | true =>
      simp only [d46871, d354136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d355456 q = 1) (hb : d356648 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d355456, d356648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d355456, d356648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d355457 q = 1) (hb : d356649 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d355457, d356649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d355457, d356649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d355458 q = 1) (hb : d356650 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d355458, d356650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d355458, d356650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d355459 q = 1) (hb : d356651 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d355459, d356651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d355459, d356651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d355472 q = 1) (hb : d356664 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d355472, d356664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d355472, d356664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h11 p ha hb
theorem andIntro96886 (p : Pattern) (ha : d355478 p = 1) (hb : d356670 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d355461 q = 1) (hb : d356653 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d355461, d356653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96882 q ha hb
    | true =>
      simp only [d355461, d356653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d355462 q = 1) (hb : d356654 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d355462, d356654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d355462, d356654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d355463 q = 1) (hb : d356655 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d355463, d356655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d355463, d356655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d355464 q = 1) (hb : d356656 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d355464, d356656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d355464, d356656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d355467 q = 1) (hb : d356659 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d355467, d356659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d355467, d356659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d355473 q = 1) (hb : d356665 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d355473, d356665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96885 q ha hb
    | true =>
      simp only [d355473, d356665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d355474 q = 1) (hb : d356666 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d355474, d356666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d355474, d356666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d355475 q = 1) (hb : d356667 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d355475, d356667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d355475, d356667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d355476 q = 1) (hb : d356668 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d355476, d356668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d355476, d356668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d355477 q = 1) (hb : d356669 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d355477, d356669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d355477, d356669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d355478 q = 1) (hb : d356670 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d355478, d356670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d355478, d356670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro96887 (p : Pattern) (ha : d355485 p = 1) (hb : d356677 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d355469 q = 1) (hb : d356661 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d355469, d356661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96883 q ha hb
    | true =>
      simp only [d355469, d356661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96884 q ha hb
  have h2 (q : Pattern) (ha : d355470 q = 1) (hb : d356662 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d355470, d356662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d355470, d356662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d355471 q = 1) (hb : d356663 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d355471, d356663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d355471, d356663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d355479 q = 1) (hb : d356671 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d355479, d356671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96884 q ha hb
    | true =>
      simp only [d355479, d356671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96886 q ha hb
  have h5 (q : Pattern) (ha : d355480 q = 1) (hb : d356672 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d355480, d356672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d355480, d356672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d355481 q = 1) (hb : d356673 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d355481, d356673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d355481, d356673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d355482 q = 1) (hb : d356674 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d355482, d356674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d355482, d356674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d355483 q = 1) (hb : d356675 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d355483, d356675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d355483, d356675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d355484 q = 1) (hb : d356676 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d355484, d356676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d355484, d356676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d355485 q = 1) (hb : d356677 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d355485, d356677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d355485, d356677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro96888 (p : Pattern) (ha : d355489 p = 1) (hb : d356681 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d355479 q = 1) (hb : d356671 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d355479, d356671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96884 q ha hb
    | true =>
      simp only [d355479, d356671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96886 q ha hb
  have h2 (q : Pattern) (ha : d355480 q = 1) (hb : d356672 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d355480, d356672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d355480, d356672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d355481 q = 1) (hb : d356673 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d355481, d356673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d355481, d356673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d355483 q = 1) (hb : d356675 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d355483, d356675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d355483, d356675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d355488 q = 1) (hb : d356680 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d355488, d356680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d355488, d356680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d355489 q = 1) (hb : d356681 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d355489, d356681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d355489, d356681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro96889 (p : Pattern) (ha : d355495 p = 1) (hb : d356687 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d355486 q = 1) (hb : d356678 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d355486, d356678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96887 q ha hb
    | true =>
      simp only [d355486, d356678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d355487 q = 1) (hb : d356679 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d355487, d356679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d355487, d356679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d355490 q = 1) (hb : d356682 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d355490, d356682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96888 q ha hb
    | true =>
      simp only [d355490, d356682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d355491 q = 1) (hb : d356683 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d355491, d356683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d355491, d356683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d355492 q = 1) (hb : d356684 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d355492, d356684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d355492, d356684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d355493 q = 1) (hb : d356685 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d355493, d356685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d355493, d356685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d355494 q = 1) (hb : d356686 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d355494, d356686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d355494, d356686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d355495 q = 1) (hb : d356687 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d355495, d356687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d355495, d356687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro96890 (p : Pattern) (ha : d355499 p = 1) (hb : d356691 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d355490 q = 1) (hb : d356682 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d355490, d356682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96888 q ha hb
    | true =>
      simp only [d355490, d356682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d355491 q = 1) (hb : d356683 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d355491, d356683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d355491, d356683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d355496 q = 1) (hb : d356688 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d355496, d356688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d355496, d356688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d355497 q = 1) (hb : d356689 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d355497, d356689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d355497, d356689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d355498 q = 1) (hb : d356690 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d355498, d356690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d355498, d356690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d355499 q = 1) (hb : d356691 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d355499, d356691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d355499, d356691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro96891 (p : Pattern) (ha : d355505 p = 1) (hb : d356697 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d355500 q = 1) (hb : d356692 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d355500, d356692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96889 q ha hb
    | true =>
      simp only [d355500, d356692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96890 q ha hb
  have h2 (q : Pattern) (ha : d355501 q = 1) (hb : d356693 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d355501, d356693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d355501, d356693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d355502 q = 1) (hb : d356694 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d355502, d356694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d355502, d356694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d355503 q = 1) (hb : d356695 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d355503, d356695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d355503, d356695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d355504 q = 1) (hb : d356696 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d355504, d356696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d355504, d356696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d355505 q = 1) (hb : d356697 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d355505, d356697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d355505, d356697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro96892 (p : Pattern) (ha : d355508 p = 1) (hb : d356700 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d355486 q = 1) (hb : d356678 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d355486, d356678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96887 q ha hb
    | true =>
      simp only [d355486, d356678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d355487 q = 1) (hb : d356679 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d355487, d356679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d355487, d356679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d355490 q = 1) (hb : d356682 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d355490, d356682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96888 q ha hb
    | true =>
      simp only [d355490, d356682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d355491 q = 1) (hb : d356683 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d355491, d356683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d355491, d356683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d355492 q = 1) (hb : d356684 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d355492, d356684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d355492, d356684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d355493 q = 1) (hb : d356685 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d355493, d356685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d355493, d356685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d355494 q = 1) (hb : d356686 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d355494, d356686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d355494, d356686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d355508 q = 1) (hb : d356700 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d355508, d356700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d355508, d356700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro96893 (p : Pattern) (ha : d355509 p = 1) (hb : d356701 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d355490 q = 1) (hb : d356682 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d355490, d356682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96888 q ha hb
    | true =>
      simp only [d355490, d356682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d355491 q = 1) (hb : d356683 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d355491, d356683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d355491, d356683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d355496 q = 1) (hb : d356688 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d355496, d356688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d355496, d356688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d355497 q = 1) (hb : d356689 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d355497, d356689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d355497, d356689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d355498 q = 1) (hb : d356690 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d355498, d356690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d355498, d356690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d355509 q = 1) (hb : d356701 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d355509, d356701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d355509, d356701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro96894 (p : Pattern) (ha : d355515 p = 1) (hb : d356707 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d355500 q = 1) (hb : d356692 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d355500, d356692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96889 q ha hb
    | true =>
      simp only [d355500, d356692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96890 q ha hb
  have h2 (q : Pattern) (ha : d355501 q = 1) (hb : d356693 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d355501, d356693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d355501, d356693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d355502 q = 1) (hb : d356694 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d355502, d356694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d355502, d356694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d355503 q = 1) (hb : d356695 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d355503, d356695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d355503, d356695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d355504 q = 1) (hb : d356696 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d355504, d356696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d355504, d356696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d355510 q = 1) (hb : d356702 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d355510, d356702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96892 q ha hb
    | true =>
      simp only [d355510, d356702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96893 q ha hb
  have h7 (q : Pattern) (ha : d355511 q = 1) (hb : d356703 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d355511, d356703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d355511, d356703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d355512 q = 1) (hb : d356704 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d355512, d356704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d355512, d356704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d355513 q = 1) (hb : d356705 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d355513, d356705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d355513, d356705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d355514 q = 1) (hb : d356706 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d355514, d356706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d355514, d356706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d355515 q = 1) (hb : d356707 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d355515, d356707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d355515, d356707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro96895 (p : Pattern) (ha : d355520 p = 1) (hb : d356712 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d355486 q = 1) (hb : d356678 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d355486, d356678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96887 q ha hb
    | true =>
      simp only [d355486, d356678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d355487 q = 1) (hb : d356679 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d355487, d356679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d355487, d356679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d355490 q = 1) (hb : d356682 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d355490, d356682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96888 q ha hb
    | true =>
      simp only [d355490, d356682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d355491 q = 1) (hb : d356683 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d355491, d356683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d355491, d356683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d355492 q = 1) (hb : d356684 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d355492, d356684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d355492, d356684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d355493 q = 1) (hb : d356685 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d355493, d356685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d355493, d356685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d355519 q = 1) (hb : d356711 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d355519, d356711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d355519, d356711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d355520 q = 1) (hb : d356712 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d355520, d356712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d355520, d356712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro96896 (p : Pattern) (ha : d355522 p = 1) (hb : d356714 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d355490 q = 1) (hb : d356682 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d355490, d356682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96888 q ha hb
    | true =>
      simp only [d355490, d356682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d355491 q = 1) (hb : d356683 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d355491, d356683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d355491, d356683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d355496 q = 1) (hb : d356688 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d355496, d356688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d355496, d356688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d355497 q = 1) (hb : d356689 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d355497, d356689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d355497, d356689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d355521 q = 1) (hb : d356713 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d355521, d356713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d355521, d356713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d355522 q = 1) (hb : d356714 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d355522, d356714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d355522, d356714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro96897 (p : Pattern) (ha : d355529 p = 1) (hb : d356721 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d355486 q = 1) (hb : d356678 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d355486, d356678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96887 q ha hb
    | true =>
      simp only [d355486, d356678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d355487 q = 1) (hb : d356679 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d355487, d356679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d355487, d356679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d355490 q = 1) (hb : d356682 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d355490, d356682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96888 q ha hb
    | true =>
      simp only [d355490, d356682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d355491 q = 1) (hb : d356683 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d355491, d356683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d355491, d356683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d355492 q = 1) (hb : d356684 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d355492, d356684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d355492, d356684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d355527 q = 1) (hb : d356719 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d355527, d356719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d355527, d356719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d355528 q = 1) (hb : d356720 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d355528, d356720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d355528, d356720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d355529 q = 1) (hb : d356721 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d355529, d356721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d355529, d356721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro96898 (p : Pattern) (ha : d355532 p = 1) (hb : d356724 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d355490 q = 1) (hb : d356682 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d355490, d356682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96888 q ha hb
    | true =>
      simp only [d355490, d356682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d355491 q = 1) (hb : d356683 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d355491, d356683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d355491, d356683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d355496 q = 1) (hb : d356688 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d355496, d356688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d355496, d356688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d355530 q = 1) (hb : d356722 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d355530, d356722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d355530, d356722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d355531 q = 1) (hb : d356723 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d355531, d356723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d355531, d356723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d355532 q = 1) (hb : d356724 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d355532, d356724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d355532, d356724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro96899 (p : Pattern) (ha : d355542 p = 1) (hb : d356733 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d355536 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d355537 q = 1) (hb : d356728 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d355537, d356728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d355537, d356728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96883 q ha hb
  have h3 (q : Pattern) (ha : d355538 q = 1) (hb : d356729 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d355538, d356729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d355538, d356729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d355539 q = 1) (hb : d356730 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d355539, d356730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d355539, d356730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d355469 q = 1) (hb : d356661 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d355469, d356661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96883 q ha hb
    | true =>
      simp only [d355469, d356661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96884 q ha hb
  have h6 (q : Pattern) (ha : d355470 q = 1) (hb : d356662 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d355470, d356662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d355470, d356662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d355471 q = 1) (hb : d356663 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d355471, d356663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d355471, d356663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d355540 q = 1) (hb : d356731 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d355540, d356731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d355540, d356731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d355479 q = 1) (hb : d356671 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d355479, d356671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96884 q ha hb
    | true =>
      simp only [d355479, d356671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96886 q ha hb
  have h10 (q : Pattern) (ha : d355480 q = 1) (hb : d356672 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d355480, d356672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d355480, d356672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d355481 q = 1) (hb : d356673 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d355481, d356673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d355481, d356673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d355482 q = 1) (hb : d356674 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d355482, d356674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d355482, d356674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d355541 q = 1) (hb : d356732 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d355541, d356732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d355541, d356732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d355542 q = 1) (hb : d356733 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d355542, d356733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d355542, d356733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h14 p ha hb
theorem andIntro96900 (p : Pattern) (ha : d355548 p = 1) (hb : d356739 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d355543 q = 1) (hb : d356734 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d355543, d356734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96899 q ha hb
    | true =>
      simp only [d355543, d356734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d355544 q = 1) (hb : d356735 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d355544, d356735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d355544, d356735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d355486 q = 1) (hb : d356678 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d355486, d356678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96887 q ha hb
    | true =>
      simp only [d355486, d356678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d355487 q = 1) (hb : d356679 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d355487, d356679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d355487, d356679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d355545 q = 1) (hb : d356736 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d355545, d356736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d355545, d356736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d355546 q = 1) (hb : d356737 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d355546, d356737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d355546, d356737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d355547 q = 1) (hb : d356738 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d355547, d356738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d355547, d356738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d355548 q = 1) (hb : d356739 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d355548, d356739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d355548, d356739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro96901 (p : Pattern) (ha : d355557 p = 1) (hb : d356742 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d355448 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d355461 q = 1) (hb : d356653 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d355461, d356653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96882 q ha hb
    | true =>
      simp only [d355461, d356653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d355462 q = 1) (hb : d356654 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d355462, d356654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d355462, d356654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h4 (q : Pattern) (ha : d355463 q = 1) (hb : d356655 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d355463, d356655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d355463, d356655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d355464 q = 1) (hb : d356656 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d355464, d356656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d355464, d356656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h6 (q : Pattern) (ha : d355465 q = 1) (hb : d356657 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d355465, d356657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d355465, d356657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d355556 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d355557 q = 1) (hb : d356742 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d355557, d356742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d355557, d356742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro96902 (p : Pattern) (ha : d355564 p = 1) (hb : d356748 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d355469 q = 1) (hb : d356661 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d355469, d356661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96883 q ha hb
    | true =>
      simp only [d355469, d356661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96884 q ha hb
  have h2 (q : Pattern) (ha : d355470 q = 1) (hb : d356662 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d355470, d356662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d355470, d356662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d355471 q = 1) (hb : d356663 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d355471, d356663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d355471, d356663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d355479 q = 1) (hb : d356671 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d355479, d356671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96884 q ha hb
    | true =>
      simp only [d355479, d356671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96886 q ha hb
  have h5 (q : Pattern) (ha : d355480 q = 1) (hb : d356672 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d355480, d356672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d355480, d356672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d355481 q = 1) (hb : d356673 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d355481, d356673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d355481, d356673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d355482 q = 1) (hb : d356674 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d355482, d356674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d355482, d356674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d355558 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d355559 q = 1) (hb : d356743 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d355559, d356743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96901 q ha hb
    | true =>
      simp only [d355559, d356743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d355560 q = 1) (hb : d356744 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d355560, d356744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d355560, d356744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d355561 q = 1) (hb : d356745 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d355561, d356745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d355561, d356745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d355562 q = 1) (hb : d356746 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d355562, d356746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d355562, d356746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d355563 q = 1) (hb : d356747 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d355563, d356747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d355563, d356747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d355564 q = 1) (hb : d356748 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d355564, d356748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d355564, d356748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h14 p ha hb
theorem andIntro96903 (p : Pattern) (ha : d355570 p = 1) (hb : d356754 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d355565 q = 1) (hb : d356749 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d355565, d356749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96902 q ha hb
    | true =>
      simp only [d355565, d356749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d355566 q = 1) (hb : d356750 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d355566, d356750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d355566, d356750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d355567 q = 1) (hb : d356751 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d355567, d356751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d355567, d356751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d355568 q = 1) (hb : d356752 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d355568, d356752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d355568, d356752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d355569 q = 1) (hb : d356753 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d355569, d356753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d355569, d356753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d355570 q = 1) (hb : d356754 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d355570, d356754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d355570, d356754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro96904 (p : Pattern) (ha : d355576 p = 1) (hb : d356760 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d355523 q = 1) (hb : d356715 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d355523, d356715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96895 q ha hb
    | true =>
      simp only [d355523, d356715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96896 q ha hb
  have h2 (q : Pattern) (ha : d355524 q = 1) (hb : d356716 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d355524, d356716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d355524, d356716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d355525 q = 1) (hb : d356717 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d355525, d356717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d355525, d356717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d355526 q = 1) (hb : d356718 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d355526, d356718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d355526, d356718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d355533 q = 1) (hb : d356725 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d355533, d356725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96897 q ha hb
    | true =>
      simp only [d355533, d356725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96898 q ha hb
  have h6 (q : Pattern) (ha : d355534 q = 1) (hb : d356726 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d355534, d356726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d355534, d356726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d355535 q = 1) (hb : d356727 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d355535, d356727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d355535, d356727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d355549 q = 1) (hb : d356740 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d355549, d356740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96900 q ha hb
    | true =>
      simp only [d355549, d356740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96889 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d355500 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d355550 q = 1) (hb : d356741 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d355550, d356741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d355550, d356741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d355571 q = 1) (hb : d356755 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d355571, d356755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96903 q ha hb
    | true =>
      simp only [d355571, d356755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d355572 q = 1) (hb : d356756 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d355572, d356756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d355572, d356756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d355573 q = 1) (hb : d356757 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d355573, d356757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d355573, d356757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d355574 q = 1) (hb : d356758 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d355574, d356758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d355574, d356758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d355575 q = 1) (hb : d356759 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d355575, d356759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d355575, d356759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d355576 q = 1) (hb : d356760 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d355576, d356760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d355576, d356760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro96905 (p : Pattern) (ha : d355577 p = 1) (hb : d356761 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d355486 q = 1) (hb : d356678 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d355486, d356678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96887 q ha hb
    | true =>
      simp only [d355486, d356678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d355487 q = 1) (hb : d356679 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d355487, d356679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d355487, d356679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d355490 q = 1) (hb : d356682 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d355490, d356682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96888 q ha hb
    | true =>
      simp only [d355490, d356682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d355491 q = 1) (hb : d356683 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d355491, d356683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d355491, d356683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d355492 q = 1) (hb : d356684 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d355492, d356684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d355492, d356684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d355493 q = 1) (hb : d356685 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d355493, d356685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d355493, d356685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d355519 q = 1) (hb : d356711 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d355519, d356711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d355519, d356711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d355577 q = 1) (hb : d356761 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d355577, d356761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d355577, d356761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro96906 (p : Pattern) (ha : d355578 p = 1) (hb : d356762 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d355490 q = 1) (hb : d356682 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d355490, d356682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96888 q ha hb
    | true =>
      simp only [d355490, d356682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d355491 q = 1) (hb : d356683 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d355491, d356683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d355491, d356683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d355496 q = 1) (hb : d356688 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d355496, d356688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d355496, d356688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d355497 q = 1) (hb : d356689 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d355497, d356689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d355497, d356689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d355521 q = 1) (hb : d356713 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d355521, d356713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d355521, d356713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d355578 q = 1) (hb : d356762 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d355578, d356762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d355578, d356762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro96907 (p : Pattern) (ha : d355583 p = 1) (hb : d356767 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d355486 q = 1) (hb : d356678 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d355486, d356678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96887 q ha hb
    | true =>
      simp only [d355486, d356678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d355487 q = 1) (hb : d356679 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d355487, d356679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d355487, d356679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d355490 q = 1) (hb : d356682 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d355490, d356682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96888 q ha hb
    | true =>
      simp only [d355490, d356682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d355491 q = 1) (hb : d356683 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d355491, d356683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d355491, d356683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d355492 q = 1) (hb : d356684 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d355492, d356684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d355492, d356684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d355527 q = 1) (hb : d356719 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d355527, d356719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d355527, d356719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d355528 q = 1) (hb : d356720 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d355528, d356720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d355528, d356720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d355583 q = 1) (hb : d356767 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d355583, d356767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d355583, d356767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro96908 (p : Pattern) (ha : d355584 p = 1) (hb : d356768 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d355490 q = 1) (hb : d356682 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d355490, d356682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96888 q ha hb
    | true =>
      simp only [d355490, d356682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d355491 q = 1) (hb : d356683 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d355491, d356683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d355491, d356683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d355496 q = 1) (hb : d356688 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d355496, d356688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d355496, d356688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d355530 q = 1) (hb : d356722 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d355530, d356722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d355530, d356722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d355531 q = 1) (hb : d356723 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d355531, d356723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d355531, d356723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d355584 q = 1) (hb : d356768 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d355584, d356768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d355584, d356768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro96909 (p : Pattern) (ha : d355588 p = 1) (hb : d356772 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d355543 q = 1) (hb : d356734 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d355543, d356734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96899 q ha hb
    | true =>
      simp only [d355543, d356734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d355544 q = 1) (hb : d356735 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d355544, d356735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d355544, d356735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d355486 q = 1) (hb : d356678 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d355486, d356678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96887 q ha hb
    | true =>
      simp only [d355486, d356678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d355487 q = 1) (hb : d356679 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d355487, d356679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d355487, d356679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d355545 q = 1) (hb : d356736 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d355545, d356736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d355545, d356736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d355546 q = 1) (hb : d356737 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d355546, d356737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d355546, d356737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d355547 q = 1) (hb : d356738 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d355547, d356738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d355547, d356738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d355588 q = 1) (hb : d356772 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d355588, d356772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d355588, d356772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro96910 (p : Pattern) (ha : d355591 p = 1) (hb : d356775 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d355565 q = 1) (hb : d356749 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d355565, d356749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96902 q ha hb
    | true =>
      simp only [d355565, d356749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d355566 q = 1) (hb : d356750 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d355566, d356750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d355566, d356750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d355567 q = 1) (hb : d356751 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d355567, d356751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d355567, d356751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d355568 q = 1) (hb : d356752 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d355568, d356752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d355568, d356752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d355569 q = 1) (hb : d356753 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d355569, d356753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d355569, d356753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d355591 q = 1) (hb : d356775 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d355591, d356775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d355591, d356775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro96911 (p : Pattern) (ha : d355597 p = 1) (hb : d356781 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d355523 q = 1) (hb : d356715 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d355523, d356715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96895 q ha hb
    | true =>
      simp only [d355523, d356715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96896 q ha hb
  have h2 (q : Pattern) (ha : d355524 q = 1) (hb : d356716 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d355524, d356716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d355524, d356716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d355525 q = 1) (hb : d356717 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d355525, d356717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d355525, d356717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d355526 q = 1) (hb : d356718 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d355526, d356718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d355526, d356718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d355533 q = 1) (hb : d356725 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d355533, d356725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96897 q ha hb
    | true =>
      simp only [d355533, d356725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96898 q ha hb
  have h6 (q : Pattern) (ha : d355534 q = 1) (hb : d356726 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d355534, d356726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d355534, d356726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d355535 q = 1) (hb : d356727 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d355535, d356727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d355535, d356727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d355549 q = 1) (hb : d356740 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d355549, d356740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96900 q ha hb
    | true =>
      simp only [d355549, d356740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96889 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d355500 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d355550 q = 1) (hb : d356741 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d355550, d356741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d355550, d356741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d355571 q = 1) (hb : d356755 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d355571, d356755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96903 q ha hb
    | true =>
      simp only [d355571, d356755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d355572 q = 1) (hb : d356756 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d355572, d356756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d355572, d356756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d355573 q = 1) (hb : d356757 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d355573, d356757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d355573, d356757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d355574 q = 1) (hb : d356758 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d355574, d356758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d355574, d356758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d355575 q = 1) (hb : d356759 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d355575, d356759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d355575, d356759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d355579 q = 1) (hb : d356763 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d355579, d356763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96905 q ha hb
    | true =>
      simp only [d355579, d356763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96906 q ha hb
  have h17 (q : Pattern) (ha : d355580 q = 1) (hb : d356764 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d355580, d356764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d355580, d356764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d355581 q = 1) (hb : d356765 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d355581, d356765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d355581, d356765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d355582 q = 1) (hb : d356766 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d355582, d356766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d355582, d356766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d355585 q = 1) (hb : d356769 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d355585, d356769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96907 q ha hb
    | true =>
      simp only [d355585, d356769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96908 q ha hb
  have h21 (q : Pattern) (ha : d355586 q = 1) (hb : d356770 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d355586, d356770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d355586, d356770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d355587 q = 1) (hb : d356771 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d355587, d356771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d355587, d356771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d355589 q = 1) (hb : d356773 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d355589, d356773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96909 q ha hb
    | true =>
      simp only [d355589, d356773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96892 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d355510 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d355590 q = 1) (hb : d356774 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d355590, d356774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d355590, d356774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d355592 q = 1) (hb : d356776 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d355592, d356776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96910 q ha hb
    | true =>
      simp only [d355592, d356776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d355593 q = 1) (hb : d356777 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d355593, d356777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d355593, d356777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d355594 q = 1) (hb : d356778 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d355594, d356778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d355594, d356778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d355595 q = 1) (hb : d356779 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d355595, d356779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d355595, d356779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d355596 q = 1) (hb : d356780 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d355596, d356780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d355596, d356780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d355597 q = 1) (hb : d356781 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d355597, d356781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d355597, d356781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro96912 (p : Pattern) (ha : d355604 p = 1) (hb : d356788 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d355500 q = 1) (hb : d356692 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d355500, d356692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96889 q ha hb
    | true =>
      simp only [d355500, d356692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96890 q ha hb
  have h2 (q : Pattern) (ha : d355501 q = 1) (hb : d356693 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d355501, d356693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d355501, d356693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d355502 q = 1) (hb : d356694 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d355502, d356694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d355502, d356694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d355503 q = 1) (hb : d356695 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d355503, d356695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d355503, d356695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d355504 q = 1) (hb : d356696 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d355504, d356696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d355504, d356696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d355599 q = 1) (hb : d356783 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d355599, d356783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96890 q ha hb
    | true =>
      simp only [d355599, d356783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d355600 q = 1) (hb : d356784 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d355600, d356784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d355600, d356784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d355601 q = 1) (hb : d356785 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d355601, d356785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d355601, d356785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d355602 q = 1) (hb : d356786 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d355602, d356786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d355602, d356786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d355603 q = 1) (hb : d356787 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d355603, d356787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d355603, d356787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d355604 q = 1) (hb : d356788 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d355604, d356788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d355604, d356788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro96913 (p : Pattern) (ha : d355610 p = 1) (hb : d356794 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d355599 q = 1) (hb : d356783 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d355599, d356783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96890 q ha hb
    | true =>
      simp only [d355599, d356783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d355600 q = 1) (hb : d356784 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d355600, d356784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d355600, d356784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d355601 q = 1) (hb : d356785 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d355601, d356785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d355601, d356785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d355602 q = 1) (hb : d356786 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d355602, d356786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d355602, d356786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d355603 q = 1) (hb : d356787 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d355603, d356787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d355603, d356787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d355605 q = 1) (hb : d356789 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d355605, d356789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96893 q ha hb
    | true =>
      simp only [d355605, d356789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d355606 q = 1) (hb : d356790 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d355606, d356790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d355606, d356790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d355607 q = 1) (hb : d356791 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d355607, d356791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d355607, d356791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d355608 q = 1) (hb : d356792 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d355608, d356792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d355608, d356792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d355609 q = 1) (hb : d356793 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d355609, d356793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d355609, d356793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d355610 q = 1) (hb : d356794 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d355610, d356794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d355610, d356794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro96914 (p : Pattern) (ha : d355617 p = 1) (hb : d356801 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d355589 q = 1) (hb : d356773 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d355589, d356773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96909 q ha hb
    | true =>
      simp only [d355589, d356773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96892 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d355510 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d355590 q = 1) (hb : d356774 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d355590, d356774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d355590, d356774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d355592 q = 1) (hb : d356776 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d355592, d356776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96910 q ha hb
    | true =>
      simp only [d355592, d356776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d355593 q = 1) (hb : d356777 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d355593, d356777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d355593, d356777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d355594 q = 1) (hb : d356778 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d355594, d356778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d355594, d356778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d355615 q = 1) (hb : d356799 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d355615, d356799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d355615, d356799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d355616 q = 1) (hb : d356800 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d355616, d356800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d355616, d356800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d355617 q = 1) (hb : d356801 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d355617, d356801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d355617, d356801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro96915 (p : Pattern) (ha : d355619 p = 1) (hb : d356803 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d355605 q = 1) (hb : d356789 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d355605, d356789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96893 q ha hb
    | true =>
      simp only [d355605, d356789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d355606 q = 1) (hb : d356790 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d355606, d356790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d355606, d356790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d355607 q = 1) (hb : d356791 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d355607, d356791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d355607, d356791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d355608 q = 1) (hb : d356792 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d355608, d356792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d355608, d356792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d355609 q = 1) (hb : d356793 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d355609, d356793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d355609, d356793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d355619 q = 1) (hb : d356803 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d355619, d356803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d355619, d356803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro96916 (p : Pattern) (ha : d355636 p = 1) (hb : d356814 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d355629 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d355628 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d355631 q = 1) (hb : d356809 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d355631, d356809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d355631, d356809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96882 q ha hb
  have h4 (q : Pattern) (ha : d355461 q = 1) (hb : d356653 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d355461, d356653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96882 q ha hb
    | true =>
      simp only [d355461, d356653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h5 (q : Pattern) (ha : d355632 q = 1) (hb : d356810 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d355632, d356810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d355632, d356810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d355462 q = 1) (hb : d356654 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d355462, d356654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d355462, d356654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h7 (q : Pattern) (ha : d355633 q = 1) (hb : d356811 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d355633, d356811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d355633, d356811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d355634 q = 1) (hb : d356812 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d355634, d356812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d355634, d356812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h9 (q : Pattern) (ha : d355635 q = 1) (hb : d356813 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d355635, d356813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d355635, d356813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d355636 q = 1) (hb : d356814 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d355636, d356814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d355636, d356814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro96917 (p : Pattern) (ha : d355641 p = 1) (hb : d356819 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d355628 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d355631 q = 1) (hb : d356809 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d355631, d356809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d355631, d356809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96882 q ha hb
  have h3 (q : Pattern) (ha : d355461 q = 1) (hb : d356653 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d355461, d356653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96882 q ha hb
    | true =>
      simp only [d355461, d356653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h4 (q : Pattern) (ha : d355632 q = 1) (hb : d356810 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d355632, d356810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d355632, d356810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d355462 q = 1) (hb : d356654 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d355462, d356654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d355462, d356654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h6 (q : Pattern) (ha : d355633 q = 1) (hb : d356811 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d355633, d356811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d355633, d356811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d355634 q = 1) (hb : d356812 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d355634, d356812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d355634, d356812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h8 (q : Pattern) (ha : d355635 q = 1) (hb : d356813 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d355635, d356813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d355635, d356813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d355640 q = 1) (hb : d356818 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d355640, d356818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d355640, d356818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h10 (q : Pattern) (ha : d355641 q = 1) (hb : d356819 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d355641, d356819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d355641, d356819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro96918 (p : Pattern) (ha : d355651 p = 1) (hb : d356829 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d355631 q = 1) (hb : d356809 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d355631, d356809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d355631, d356809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96882 q ha hb
  have h2 (q : Pattern) (ha : d355461 q = 1) (hb : d356653 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d355461, d356653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96882 q ha hb
    | true =>
      simp only [d355461, d356653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d355632 q = 1) (hb : d356810 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d355632, d356810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d355632, d356810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d355462 q = 1) (hb : d356654 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d355462, d356654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d355462, d356654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d355633 q = 1) (hb : d356811 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d355633, d356811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d355633, d356811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d355634 q = 1) (hb : d356812 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d355634, d356812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d355634, d356812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d355640 q = 1) (hb : d356818 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d355640, d356818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d355640, d356818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d355646 q = 1) (hb : d356824 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d355646, d356824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d355646, d356824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96885 q ha hb
  have h9 (q : Pattern) (ha : d355473 q = 1) (hb : d356665 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d355473, d356665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96885 q ha hb
    | true =>
      simp only [d355473, d356665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d355647 q = 1) (hb : d356825 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d355647, d356825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d355647, d356825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d355474 q = 1) (hb : d356666 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d355474, d356666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d355474, d356666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d355648 q = 1) (hb : d356826 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d355648, d356826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d355648, d356826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d355649 q = 1) (hb : d356827 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d355649, d356827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d355649, d356827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d355650 q = 1) (hb : d356828 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d355650, d356828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d355650, d356828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d355651 q = 1) (hb : d356829 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d355651, d356829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d355651, d356829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro96919 (p : Pattern) (ha : d355657 p = 1) (hb : d356835 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d355630 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d355637 q = 1) (hb : d356815 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d355637, d356815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d355637, d356815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96916 q ha hb
  have h3 (q : Pattern) (ha : d355638 q = 1) (hb : d356816 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d355638, d356816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d355638, d356816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d355639 q = 1) (hb : d356817 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d355639, d356817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d355639, d356817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d355642 q = 1) (hb : d356820 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d355642, d356820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96916 q ha hb
    | true =>
      simp only [d355642, d356820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96917 q ha hb
  have h6 (q : Pattern) (ha : d355643 q = 1) (hb : d356821 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d355643, d356821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d355643, d356821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d355644 q = 1) (hb : d356822 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d355644, d356822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d355644, d356822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d355645 q = 1) (hb : d356823 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d355645, d356823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d355645, d356823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d355652 q = 1) (hb : d356830 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d355652, d356830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96917 q ha hb
    | true =>
      simp only [d355652, d356830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96918 q ha hb
  have h10 (q : Pattern) (ha : d355653 q = 1) (hb : d356831 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d355653, d356831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d355653, d356831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d355654 q = 1) (hb : d356832 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d355654, d356832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d355654, d356832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d355655 q = 1) (hb : d356833 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d355655, d356833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d355655, d356833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d355656 q = 1) (hb : d356834 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d355656, d356834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d355656, d356834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d355657 q = 1) (hb : d356835 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d355657, d356835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d355657, d356835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h14 p ha hb
theorem andIntro96920 (p : Pattern) (ha : d355662 p = 1) (hb : d356840 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d355642 q = 1) (hb : d356820 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d355642, d356820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96916 q ha hb
    | true =>
      simp only [d355642, d356820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96917 q ha hb
  have h2 (q : Pattern) (ha : d355643 q = 1) (hb : d356821 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d355643, d356821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d355643, d356821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d355644 q = 1) (hb : d356822 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d355644, d356822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d355644, d356822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d355652 q = 1) (hb : d356830 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d355652, d356830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96917 q ha hb
    | true =>
      simp only [d355652, d356830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96918 q ha hb
  have h5 (q : Pattern) (ha : d355653 q = 1) (hb : d356831 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d355653, d356831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d355653, d356831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d355654 q = 1) (hb : d356832 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d355654, d356832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d355654, d356832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d355655 q = 1) (hb : d356833 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d355655, d356833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d355655, d356833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d355660 q = 1) (hb : d356838 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d355660, d356838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d355660, d356838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d355661 q = 1) (hb : d356839 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d355661, d356839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d355661, d356839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d355662 q = 1) (hb : d356840 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d355662, d356840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d355662, d356840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro96921 (p : Pattern) (ha : d355668 p = 1) (hb : d356846 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d355658 q = 1) (hb : d356836 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d355658, d356836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96919 q ha hb
    | true =>
      simp only [d355658, d356836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d355659 q = 1) (hb : d356837 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d355659, d356837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d355659, d356837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d355663 q = 1) (hb : d356841 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d355663, d356841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96920 q ha hb
    | true =>
      simp only [d355663, d356841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d355664 q = 1) (hb : d356842 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d355664, d356842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d355664, d356842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d355665 q = 1) (hb : d356843 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d355665, d356843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d355665, d356843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d355666 q = 1) (hb : d356844 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d355666, d356844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d355666, d356844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d355667 q = 1) (hb : d356845 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d355667, d356845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d355667, d356845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d355668 q = 1) (hb : d356846 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d355668, d356846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d355668, d356846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro96922 (p : Pattern) (ha : d355670 p = 1) (hb : d356848 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d355652 q = 1) (hb : d356830 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d355652, d356830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96917 q ha hb
    | true =>
      simp only [d355652, d356830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96918 q ha hb
  have h2 (q : Pattern) (ha : d355653 q = 1) (hb : d356831 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d355653, d356831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d355653, d356831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d355654 q = 1) (hb : d356832 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d355654, d356832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d355654, d356832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d355660 q = 1) (hb : d356838 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d355660, d356838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d355660, d356838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d355669 q = 1) (hb : d356847 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d355669, d356847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d355669, d356847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d355670 q = 1) (hb : d356848 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d355670, d356848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d355670, d356848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro96923 (p : Pattern) (ha : d355676 p = 1) (hb : d356854 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d355663 q = 1) (hb : d356841 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d355663, d356841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96920 q ha hb
    | true =>
      simp only [d355663, d356841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d355664 q = 1) (hb : d356842 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d355664, d356842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d355664, d356842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d355671 q = 1) (hb : d356849 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d355671, d356849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96922 q ha hb
    | true =>
      simp only [d355671, d356849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d355672 q = 1) (hb : d356850 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d355672, d356850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d355672, d356850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d355673 q = 1) (hb : d356851 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d355673, d356851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d355673, d356851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d355674 q = 1) (hb : d356852 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d355674, d356852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d355674, d356852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d355675 q = 1) (hb : d356853 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d355675, d356853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d355675, d356853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d355676 q = 1) (hb : d356854 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d355676, d356854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d355676, d356854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro96924 (p : Pattern) (ha : d355689 p = 1) (hb : d356857 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d355628 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d355631 q = 1) (hb : d356809 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d355631, d356809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d355631, d356809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96882 q ha hb
  have h3 (q : Pattern) (ha : d355461 q = 1) (hb : d356653 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d355461, d356653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96882 q ha hb
    | true =>
      simp only [d355461, d356653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h4 (q : Pattern) (ha : d355632 q = 1) (hb : d356810 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d355632, d356810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d355632, d356810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d355462 q = 1) (hb : d356654 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d355462, d356654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d355462, d356654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h6 (q : Pattern) (ha : d355633 q = 1) (hb : d356811 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d355633, d356811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d355633, d356811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d355634 q = 1) (hb : d356812 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d355634, d356812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d355634, d356812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h8 (q : Pattern) (ha : d355635 q = 1) (hb : d356813 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d355635, d356813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d355635, d356813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d355688 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d355689 q = 1) (hb : d356857 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d355689, d356857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d355689, d356857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  exact h10 p ha hb
theorem andIntro96925 (p : Pattern) (ha : d355696 p = 1) (hb : d356863 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d355642 q = 1) (hb : d356820 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d355642, d356820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96916 q ha hb
    | true =>
      simp only [d355642, d356820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96917 q ha hb
  have h2 (q : Pattern) (ha : d355643 q = 1) (hb : d356821 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d355643, d356821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d355643, d356821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d355644 q = 1) (hb : d356822 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d355644, d356822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d355644, d356822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d355652 q = 1) (hb : d356830 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d355652, d356830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96917 q ha hb
    | true =>
      simp only [d355652, d356830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96918 q ha hb
  have h5 (q : Pattern) (ha : d355653 q = 1) (hb : d356831 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d355653, d356831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d355653, d356831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d355654 q = 1) (hb : d356832 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d355654, d356832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d355654, d356832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d355655 q = 1) (hb : d356833 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d355655, d356833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d355655, d356833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d355690 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d355691 q = 1) (hb : d356858 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d355691, d356858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96924 q ha hb
    | true =>
      simp only [d355691, d356858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d355692 q = 1) (hb : d356859 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d355692, d356859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d355692, d356859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d355693 q = 1) (hb : d356860 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d355693, d356860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d355693, d356860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d355694 q = 1) (hb : d356861 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d355694, d356861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d355694, d356861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d355695 q = 1) (hb : d356862 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d355695, d356862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d355695, d356862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d355696 q = 1) (hb : d356863 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d355696, d356863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d355696, d356863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h14 p ha hb
theorem andIntro96926 (p : Pattern) (ha : d355702 p = 1) (hb : d356869 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d355697 q = 1) (hb : d356864 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d355697, d356864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96925 q ha hb
    | true =>
      simp only [d355697, d356864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d355698 q = 1) (hb : d356865 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d355698, d356865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d355698, d356865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d355699 q = 1) (hb : d356866 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d355699, d356866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d355699, d356866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d355700 q = 1) (hb : d356867 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d355700, d356867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d355700, d356867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d355701 q = 1) (hb : d356868 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d355701, d356868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d355701, d356868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d355702 q = 1) (hb : d356869 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d355702, d356869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d355702, d356869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro96927 (p : Pattern) (ha : d355708 p = 1) (hb : d356875 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d355677 q = 1) (hb : d356855 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d355677, d356855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96921 q ha hb
    | true =>
      simp only [d355677, d356855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96923 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d355682 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d355683 q = 1) (hb : d356856 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d355683, d356856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d355683, d356856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d355703 q = 1) (hb : d356870 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d355703, d356870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96926 q ha hb
    | true =>
      simp only [d355703, d356870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d355704 q = 1) (hb : d356871 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d355704, d356871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d355704, d356871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d355705 q = 1) (hb : d356872 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d355705, d356872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d355705, d356872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d355706 q = 1) (hb : d356873 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d355706, d356873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d355706, d356873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d355707 q = 1) (hb : d356874 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d355707, d356874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d355707, d356874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d355708 q = 1) (hb : d356875 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d355708, d356875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d355708, d356875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro96928 (p : Pattern) (ha : d355681 p = 1) (hb : d356880 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d355671 q = 1) (hb : d356849 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d355671, d356849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96922 q ha hb
    | true =>
      simp only [d355671, d356849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d355672 q = 1) (hb : d356850 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d355672, d356850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d355672, d356850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d355678 q = 1) (hb : d356877 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d355678, d356877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d355678, d356877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d355679 q = 1) (hb : d356878 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d355679, d356878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d355679, d356878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d355680 q = 1) (hb : d356879 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d355680, d356879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d355680, d356879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d355681 q = 1) (hb : d356880 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d355681, d356880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d355681, d356880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro96929 (p : Pattern) (ha : d355715 p = 1) (hb : d356886 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d355710 q = 1) (hb : d356881 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d355710, d356881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96928 q ha hb
    | true =>
      simp only [d355710, d356881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d355711 q = 1) (hb : d356882 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d355711, d356882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d355711, d356882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d355712 q = 1) (hb : d356883 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d355712, d356883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d355712, d356883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d355713 q = 1) (hb : d356884 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d355713, d356884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d355713, d356884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d355714 q = 1) (hb : d356885 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d355714, d356885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d355714, d356885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d355715 q = 1) (hb : d356886 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d355715, d356886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d355715, d356886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro96930 (p : Pattern) (ha : d355721 p = 1) (hb : d356892 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d355506 q = 1) (hb : d356698 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d355506, d356698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d355506, d356698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96891 q ha hb
  have h2 (q : Pattern) (ha : d355507 q = 1) (hb : d356699 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d355507, d356699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d355507, d356699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d355516 q = 1) (hb : d356708 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d355516, d356708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96891 q ha hb
    | true =>
      simp only [d355516, d356708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96894 q ha hb
  have h4 (q : Pattern) (ha : d355517 q = 1) (hb : d356709 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d355517, d356709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d355517, d356709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d355518 q = 1) (hb : d356710 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d355518, d356710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d355518, d356710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d355598 q = 1) (hb : d356782 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d355598, d356782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96904 q ha hb
    | true =>
      simp only [d355598, d356782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96911 q ha hb
  have h7 (q : Pattern) (ha : d355611 q = 1) (hb : d356795 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d355611, d356795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96912 q ha hb
    | true =>
      simp only [d355611, d356795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96913 q ha hb
  have h8 (q : Pattern) (ha : d355612 q = 1) (hb : d356796 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d355612, d356796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d355612, d356796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d355613 q = 1) (hb : d356797 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d355613, d356797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d355613, d356797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d355614 q = 1) (hb : d356798 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d355614, d356798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d355614, d356798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d355618 q = 1) (hb : d356802 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d355618, d356802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d355618, d356802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96914 q ha hb
  have h12 (q : Pattern) (ha : d355620 q = 1) (hb : d356804 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d355620, d356804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d355620, d356804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96915 q ha hb
  have h13 (q : Pattern) (ha : d355621 q = 1) (hb : d356805 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d355621, d356805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d355621, d356805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d355622 q = 1) (hb : d356806 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d355622, d356806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d355622, d356806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d355623 q = 1) (hb : d356807 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d355623, d356807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d355623, d356807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d355624 q = 1) (hb : d356808 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d355624, d356808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d355624, d356808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d355709 q = 1) (hb : d356876 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d355709, d356876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d355709, d356876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96927 q ha hb
  have h18 (q : Pattern) (ha : d355716 q = 1) (hb : d356887 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d355716, d356887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d355716, d356887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96929 q ha hb
  have h19 (q : Pattern) (ha : d355717 q = 1) (hb : d356888 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d355717, d356888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d355717, d356888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d355718 q = 1) (hb : d356889 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d355718, d356889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d355718, d356889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d355719 q = 1) (hb : d356890 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d355719, d356890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d355719, d356890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d355720 q = 1) (hb : d356891 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d355720, d356891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d355720, d356891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d355721 q = 1) (hb : d356892 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d355721, d356892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d355721, d356892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro96931 (p : Pattern) (ha : d355727 p = 1) (hb : d356898 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d355722 q = 1) (hb : d356893 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d355722, d356893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d355722, d356893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96930 q ha hb
  have h2 (q : Pattern) (ha : d355723 q = 1) (hb : d356894 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d355723, d356894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d355723, d356894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d355724 q = 1) (hb : d356895 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d355724, d356895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d355724, d356895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d355725 q = 1) (hb : d356896 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d355725, d356896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d355725, d356896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d355726 q = 1) (hb : d356897 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d355726, d356897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d355726, d356897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d355727 q = 1) (hb : d356898 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d355727, d356898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d355727, d356898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro96932 (p : Pattern) (ha : d355733 p = 1) (hb : d356904 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d354507 q = 1) (hb : d356147 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d354507, d356147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96752 q ha hb
    | true =>
      simp only [d354507, d356147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96781 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d354751 q = 1) (hb : d356385 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d354751, d356385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d354751, d356385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96827 q ha hb
  have h3 (q : Pattern) (ha : d354752 q = 1) (hb : d356386 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d354752, d356386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d354752, d356386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d355035 q = 1) (hb : d356642 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d355035, d356642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d355035, d356642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96880 q ha hb
  have h5 (q : Pattern) (ha : d355036 q = 1) (hb : d356643 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d355036, d356643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d355036, d356643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d355037 q = 1) (hb : d356644 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d355037, d356644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d355037, d356644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d355435 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d355436 q = 1) (hb : d356645 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d355436, d356645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d355436, d356645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d355728 q = 1) (hb : d356899 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d355728, d356899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d355728, d356899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96931 q ha hb
  have h10 (q : Pattern) (ha : d355729 q = 1) (hb : d356900 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d355729, d356900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d355729, d356900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d355730 q = 1) (hb : d356901 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d355730, d356901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d355730, d356901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d355731 q = 1) (hb : d356902 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d355731, d356902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d355731, d356902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d355732 q = 1) (hb : d356903 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d355732, d356903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d355732, d356903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d355733 q = 1) (hb : d356904 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d355733, d356904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d355733, d356904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h14 p ha hb
theorem andIntro96933 (p : Pattern) (ha : d355739 p = 1) (hb : d356910 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d355734 q = 1) (hb : d356905 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d355734, d356905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96932 q ha hb
    | true =>
      simp only [d355734, d356905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d355735 q = 1) (hb : d356906 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d355735, d356906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d355735, d356906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d355736 q = 1) (hb : d356907 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d355736, d356907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d355736, d356907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d355737 q = 1) (hb : d356908 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d355737, d356908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d355737, d356908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d355738 q = 1) (hb : d356909 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d355738, d356909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d355738, d356909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d355739 q = 1) (hb : d356910 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d355739, d356910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d355739, d356910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro96934 (p : Pattern) (ha : d355745 p = 1) (hb : d356916 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d355740 q = 1) (hb : d356911 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d355740, d356911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96933 q ha hb
    | true =>
      simp only [d355740, d356911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d355741 q = 1) (hb : d356912 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d355741, d356912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d355741, d356912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d355742 q = 1) (hb : d356913 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d355742, d356913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d355742, d356913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d355743 q = 1) (hb : d356914 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d355743, d356914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d355743, d356914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d355744 q = 1) (hb : d356915 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d355744, d356915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d355744, d356915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d355745 q = 1) (hb : d356916 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d355745, d356916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d355745, d356916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro96935 (p : Pattern) (ha : d355751 p = 1) (hb : d356922 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d355746 q = 1) (hb : d356917 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d355746, d356917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96934 q ha hb
    | true =>
      simp only [d355746, d356917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d355747 q = 1) (hb : d356918 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d355747, d356918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d355747, d356918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d355748 q = 1) (hb : d356919 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d355748, d356919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d355748, d356919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d355749 q = 1) (hb : d356920 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d355749, d356920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d355749, d356920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d355750 q = 1) (hb : d356921 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d355750, d356921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d355750, d356921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d355751 q = 1) (hb : d356922 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d355751, d356922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d355751, d356922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro96936 (p : Pattern) (ha : d355757 p = 1) (hb : d356928 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d355752 q = 1) (hb : d356923 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d355752, d356923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96935 q ha hb
    | true =>
      simp only [d355752, d356923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d355753 q = 1) (hb : d356924 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d355753, d356924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d355753, d356924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d355754 q = 1) (hb : d356925 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d355754, d356925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d355754, d356925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d355755 q = 1) (hb : d356926 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d355755, d356926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d355755, d356926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d355756 q = 1) (hb : d356927 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d355756, d356927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d355756, d356927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d355757 q = 1) (hb : d356928 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d355757, d356928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d355757, d356928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro96937 (p : Pattern) (ha : d355763 p = 1) (hb : d356934 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d355758 q = 1) (hb : d356929 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d355758, d356929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96936 q ha hb
    | true =>
      simp only [d355758, d356929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d355759 q = 1) (hb : d356930 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d355759, d356930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d355759, d356930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d355760 q = 1) (hb : d356931 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d355760, d356931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d355760, d356931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d355761 q = 1) (hb : d356932 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d355761, d356932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d355761, d356932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d355762 q = 1) (hb : d356933 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d355762, d356933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d355762, d356933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d355763 q = 1) (hb : d356934 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d355763, d356934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d355763, d356934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro96938 (p : Pattern) (ha : d355769 p = 1) (hb : d356940 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d355764 q = 1) (hb : d356935 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d355764, d356935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96937 q ha hb
    | true =>
      simp only [d355764, d356935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d355765 q = 1) (hb : d356936 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d355765, d356936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d355765, d356936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d355766 q = 1) (hb : d356937 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d355766, d356937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d355766, d356937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d355767 q = 1) (hb : d356938 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d355767, d356938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d355767, d356938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d355768 q = 1) (hb : d356939 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d355768, d356939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d355768, d356939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d355769 q = 1) (hb : d356940 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d355769, d356940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d355769, d356940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro96939 (p : Pattern) (ha : d355775 p = 1) (hb : d356946 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d355770 q = 1) (hb : d356941 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d355770, d356941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96938 q ha hb
    | true =>
      simp only [d355770, d356941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d355771 q = 1) (hb : d356942 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d355771, d356942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d355771, d356942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d355772 q = 1) (hb : d356943 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d355772, d356943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d355772, d356943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d355773 q = 1) (hb : d356944 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d355773, d356944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d355773, d356944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d355774 q = 1) (hb : d356945 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d355774, d356945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d355774, d356945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d355775 q = 1) (hb : d356946 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d355775, d356946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d355775, d356946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro96940 (p : Pattern) (ha : d46864 p = 1) (hb : d53647 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96425 q ha hb
    | true =>
      simp only [d112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96426 q ha hb
  have h2 (q : Pattern) (ha : d113 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d46864 q = 1) (hb : d53637 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d53637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d46864 q = 1) (hb : d53638 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d407 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96446 q ha hb
  have h6 (q : Pattern) (ha : d46864 q = 1) (hb : d53639 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d53639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d46864 q = 1) (hb : d53640 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d46864 q = 1) (hb : d53641 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d46864 q = 1) (hb : d53642 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d463 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96447 q ha hb
  have h11 (q : Pattern) (ha : d46864 q = 1) (hb : d53643 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d53643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d46864 q = 1) (hb : d53644 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d53644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d46864 q = 1) (hb : d53645 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d46864 q = 1) (hb : d53646 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d53646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d46864 q = 1) (hb : d53647 q = 1) : d0 q = 1 := by
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
theorem andIntro96941 (p : Pattern) (ha : d46864 p = 1) (hb : d290066 p = 1) : d356088 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d40183 q = 1) (hb : d46864 q = 1) : d355806 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d40183, d355806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96438 q ha hb
    | true =>
      simp only [d40183, d355806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96417 q ha hb
  have h2 (q : Pattern) (ha : d40243 q = 1) (hb : d46864 q = 1) : d355864 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d40243, d355864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40243, d355864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d40244 q = 1) (hb : d46864 q = 1) : d355865 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d40244, d355865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d40244, d355865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d40245 q = 1) (hb : d46864 q = 1) : d355866 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d40245, d355866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40245, d355866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d40246 q = 1) (hb : d46864 q = 1) : d355867 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d40246, d355867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40246, d355867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d46864 q = 1) (hb : d290066 q = 1) : d356088 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d290066, d356088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d290066, d356088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro96942 (p : Pattern) (ha : d46864 p = 1) (hb : d290076 p = 1) : d356134 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d40219 q = 1) (hb : d46864 q = 1) : d355840 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d40219, d355840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96443 q ha hb
    | true =>
      simp only [d40219, d355840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96422 q ha hb
  have h2 (q : Pattern) (ha : d46864 q = 1) (hb : d290072 q = 1) : d356130 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d290072, d356130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d290072, d356130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d46864 q = 1) (hb : d290073 q = 1) : d356131 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d290073, d356131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d290073, d356131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d46864 q = 1) (hb : d290074 q = 1) : d356132 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d290074, d356132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d290074, d356132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d46864 q = 1) (hb : d290075 q = 1) : d356133 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d290075, d356133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d290075, d356133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d46864 q = 1) (hb : d290076 q = 1) : d356134 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d290076, d356134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d290076, d356134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro96943 (p : Pattern) (ha : d46864 p = 1) (hb : d290082 p = 1) : d356957 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d40248 q = 1) (hb : d46864 q = 1) : d355869 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d40248, d355869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96448 q ha hb
    | true =>
      simp only [d40248, d355869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96449 q ha hb
  have h2 (q : Pattern) (ha : d40249 q = 1) (hb : d46864 q = 1) : d355870 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d40249, d355870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d40249, d355870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d46864 q = 1) (hb : d290064 q = 1) : d356947 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d290064, d356947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d290064, d356947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d46864 q = 1) (hb : d290065 q = 1) : d356948 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d290065, d356948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d290065, d356948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d46864 q = 1) (hb : d290067 q = 1) : d356089 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d290067, d356089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d290067, d356089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96941 q ha hb
  have h6 (q : Pattern) (ha : d46864 q = 1) (hb : d290068 q = 1) : d356949 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d290068, d356949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d290068, d356949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d46864 q = 1) (hb : d290069 q = 1) : d356950 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d290069, d356950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d290069, d356950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d46864 q = 1) (hb : d290070 q = 1) : d356951 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d290070, d356951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d290070, d356951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d46864 q = 1) (hb : d290071 q = 1) : d356952 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d290071, d356952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d290071, d356952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d46864 q = 1) (hb : d290077 q = 1) : d356135 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d290077, d356135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d290077, d356135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96942 q ha hb
  have h11 (q : Pattern) (ha : d46864 q = 1) (hb : d290078 q = 1) : d356953 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d290078, d356953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d290078, d356953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d46864 q = 1) (hb : d290079 q = 1) : d356954 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d290079, d356954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d290079, d356954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d46864 q = 1) (hb : d290080 q = 1) : d356955 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d290080, d356955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d290080, d356955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d46864 q = 1) (hb : d290081 q = 1) : d356956 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d290081, d356956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d290081, d356956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d46864 q = 1) (hb : d290082 q = 1) : d356957 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d290082, d356957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d290082, d356957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro96944 (p : Pattern) (ha : d46864 p = 1) (hb : d290088 p = 1) : d356963 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46864 q = 1) (hb : d53648 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96940 q ha hb
  have h2 (q : Pattern) (ha : d46864 q = 1) (hb : d53649 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d46864 q = 1) (hb : d53650 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d46864 q = 1) (hb : d53651 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d46864 q = 1) (hb : d53652 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d46864 q = 1) (hb : d290083 q = 1) : d356958 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d290083, d356958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d290083, d356958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96943 q ha hb
  have h7 (q : Pattern) (ha : d46864 q = 1) (hb : d290084 q = 1) : d356959 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d290084, d356959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d290084, d356959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d46864 q = 1) (hb : d290085 q = 1) : d356960 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d290085, d356960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d290085, d356960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d46864 q = 1) (hb : d290086 q = 1) : d356961 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d290086, d356961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d290086, d356961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d46864 q = 1) (hb : d290087 q = 1) : d356962 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d290087, d356962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d290087, d356962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d46864 q = 1) (hb : d290088 q = 1) : d356963 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d290088, d356963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d290088, d356963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro96945 (p : Pattern) (ha : d46864 p = 1) (hb : d290091 p = 1) : d356966 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d40465 q = 1) (hb : d46864 q = 1) : d355926 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d40465, d355926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96479 q ha hb
    | true =>
      simp only [d40465, d355926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96480 q ha hb
  have h2 (q : Pattern) (ha : d40466 q = 1) (hb : d46864 q = 1) : d355989 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d40466, d355989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40466, d355989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d40467 q = 1) (hb : d46864 q = 1) : d355990 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d40467, d355990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d40467, d355990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d40468 q = 1) (hb : d46864 q = 1) : d355991 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d40468, d355991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40468, d355991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d40469 q = 1) (hb : d46864 q = 1) : d355992 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d40469, d355992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40469, d355992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d46864 q = 1) (hb : d290091 q = 1) : d356966 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d290091, d356966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d290091, d356966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro96946 (p : Pattern) (ha : d46864 p = 1) (hb : d290102 p = 1) : d356976 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46864 q = 1) (hb : d290097 q = 1) : d355964 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d290097, d355964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96516 q hb ha
    | true =>
      simp only [d290097, d355964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96486 q hb ha
  have h2 (q : Pattern) (ha : d46864 q = 1) (hb : d290098 q = 1) : d356972 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d290098, d356972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d290098, d356972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d46864 q = 1) (hb : d290099 q = 1) : d356973 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d290099, d356973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d290099, d356973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d46864 q = 1) (hb : d290100 q = 1) : d356974 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d290100, d356974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d290100, d356974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d46864 q = 1) (hb : d290101 q = 1) : d356975 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d290101, d356975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d290101, d356975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d46864 q = 1) (hb : d290102 q = 1) : d356976 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d290102, d356976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d290102, d356976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro96947 (p : Pattern) (ha : d46864 p = 1) (hb : d290108 p = 1) : d356982 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d40471 q = 1) (hb : d46864 q = 1) : d355994 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d40471, d355994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96478 q ha hb
    | true =>
      simp only [d40471, d355994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96481 q ha hb
  have h2 (q : Pattern) (ha : d40472 q = 1) (hb : d46864 q = 1) : d355995 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d40472, d355995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d40472, d355995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d46864 q = 1) (hb : d290089 q = 1) : d356964 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d290089, d356964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d290089, d356964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d46864 q = 1) (hb : d290090 q = 1) : d356965 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d290090, d356965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d290090, d356965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d46864 q = 1) (hb : d290092 q = 1) : d356967 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d290092, d356967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d290092, d356967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96945 q ha hb
  have h6 (q : Pattern) (ha : d46864 q = 1) (hb : d290093 q = 1) : d356968 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d290093, d356968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d290093, d356968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d46864 q = 1) (hb : d290094 q = 1) : d356969 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d290094, d356969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d290094, d356969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d46864 q = 1) (hb : d290095 q = 1) : d356970 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d290095, d356970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d290095, d356970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d46864 q = 1) (hb : d290096 q = 1) : d356971 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d290096, d356971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d290096, d356971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d46864 q = 1) (hb : d290103 q = 1) : d356977 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d290103, d356977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d290103, d356977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96946 q ha hb
  have h11 (q : Pattern) (ha : d46864 q = 1) (hb : d290104 q = 1) : d356978 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d290104, d356978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d290104, d356978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d46864 q = 1) (hb : d290105 q = 1) : d356979 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d290105, d356979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d290105, d356979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d46864 q = 1) (hb : d290106 q = 1) : d356980 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d290106, d356980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d290106, d356980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d46864 q = 1) (hb : d290107 q = 1) : d356981 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d290107, d356981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d290107, d356981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d46864 q = 1) (hb : d290108 q = 1) : d356982 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d290108, d356982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d290108, d356982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro96948 (p : Pattern) (ha : d46864 p = 1) (hb : d290114 p = 1) : d356988 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46864 q = 1) (hb : d290109 q = 1) : d356983 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d290109, d356983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d290109, d356983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96947 q ha hb
  have h2 (q : Pattern) (ha : d46864 q = 1) (hb : d290110 q = 1) : d356984 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d290110, d356984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d290110, d356984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d46864 q = 1) (hb : d290111 q = 1) : d356985 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d290111, d356985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d290111, d356985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d46864 q = 1) (hb : d290112 q = 1) : d356986 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d290112, d356986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d290112, d356986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d46864 q = 1) (hb : d290113 q = 1) : d356987 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d290113, d356987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d290113, d356987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d46864 q = 1) (hb : d290114 q = 1) : d356988 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d290114, d356988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d290114, d356988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro96949 (p : Pattern) (ha : d46864 p = 1) (hb : d290118 p = 1) : d356992 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d40804 q = 1) (hb : d46864 q = 1) : d356175 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d40804, d356175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96530 q ha hb
    | true =>
      simp only [d40804, d356175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96531 q ha hb
  have h2 (q : Pattern) (ha : d40805 q = 1) (hb : d46864 q = 1) : d356176 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d40805, d356176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40805, d356176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d40806 q = 1) (hb : d46864 q = 1) : d356177 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d40806, d356177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d40806, d356177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d40807 q = 1) (hb : d46864 q = 1) : d356178 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d40807, d356178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40807, d356178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d40808 q = 1) (hb : d46864 q = 1) : d356179 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d40808, d356179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d40808, d356179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d46864 q = 1) (hb : d290118 q = 1) : d356992 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d290118, d356992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d290118, d356992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro96950 (p : Pattern) (ha : d46864 p = 1) (hb : d290129 p = 1) : d357003 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46864 q = 1) (hb : d290124 q = 1) : d356998 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d290124, d356998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96571 q hb ha
    | true =>
      simp only [d290124, d356998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96539 q hb ha
  have h2 (q : Pattern) (ha : d46864 q = 1) (hb : d290125 q = 1) : d356999 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d290125, d356999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d290125, d356999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d46864 q = 1) (hb : d290126 q = 1) : d357000 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d290126, d357000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d290126, d357000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d46864 q = 1) (hb : d290127 q = 1) : d357001 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d290127, d357001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d290127, d357001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d46864 q = 1) (hb : d290128 q = 1) : d357002 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d290128, d357002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d290128, d357002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d46864 q = 1) (hb : d290129 q = 1) : d357003 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d290129, d357003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d290129, d357003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro96951 (p : Pattern) (ha : d46864 p = 1) (hb : d290135 p = 1) : d357009 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d40810 q = 1) (hb : d46864 q = 1) : d356181 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d40810, d356181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96529 q ha hb
    | true =>
      simp only [d40810, d356181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96532 q ha hb
  have h2 (q : Pattern) (ha : d40811 q = 1) (hb : d46864 q = 1) : d356182 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d40811, d356182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d40811, d356182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d46864 q = 1) (hb : d290116 q = 1) : d356990 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d290116, d356990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d290116, d356990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d46864 q = 1) (hb : d290117 q = 1) : d356991 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d290117, d356991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d290117, d356991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d46864 q = 1) (hb : d290119 q = 1) : d356993 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d290119, d356993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d290119, d356993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96949 q ha hb
  have h6 (q : Pattern) (ha : d46864 q = 1) (hb : d290120 q = 1) : d356994 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d290120, d356994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d290120, d356994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d46864 q = 1) (hb : d290121 q = 1) : d356995 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d290121, d356995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d290121, d356995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d46864 q = 1) (hb : d290122 q = 1) : d356996 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d290122, d356996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d290122, d356996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d46864 q = 1) (hb : d290123 q = 1) : d356997 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d290123, d356997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d290123, d356997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d46864 q = 1) (hb : d290130 q = 1) : d357004 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d290130, d357004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d290130, d357004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96950 q ha hb
  have h11 (q : Pattern) (ha : d46864 q = 1) (hb : d290131 q = 1) : d357005 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d290131, d357005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d290131, d357005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d46864 q = 1) (hb : d290132 q = 1) : d357006 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d290132, d357006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d290132, d357006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d46864 q = 1) (hb : d290133 q = 1) : d357007 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d290133, d357007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d290133, d357007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d46864 q = 1) (hb : d290134 q = 1) : d357008 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d290134, d357008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d290134, d357008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d46864 q = 1) (hb : d290135 q = 1) : d357009 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d290135, d357009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d290135, d357009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro96952 (p : Pattern) (ha : d46864 p = 1) (hb : d290141 p = 1) : d357015 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46864 q = 1) (hb : d290136 q = 1) : d357010 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d290136, d357010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d290136, d357010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96951 q ha hb
  have h2 (q : Pattern) (ha : d46864 q = 1) (hb : d290137 q = 1) : d357011 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d290137, d357011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d290137, d357011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d46864 q = 1) (hb : d290138 q = 1) : d357012 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d290138, d357012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d290138, d357012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d46864 q = 1) (hb : d290139 q = 1) : d357013 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d290139, d357013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d290139, d357013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d46864 q = 1) (hb : d290140 q = 1) : d357014 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d290140, d357014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d290140, d357014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d46864 q = 1) (hb : d290141 q = 1) : d357015 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d290141, d357015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d290141, d357015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro96953 (p : Pattern) (ha : d46864 p = 1) (hb : d333402 p = 1) : d357050 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d39765 q = 1) (hb : d46864 q = 1) : d356702 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d39765, d356702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96362 q ha hb
    | true =>
      simp only [d39765, d356702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96363 q ha hb
  have h2 (q : Pattern) (ha : d39766 q = 1) (hb : d46864 q = 1) : d356703 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d39766, d356703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39766, d356703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39767 q = 1) (hb : d46864 q = 1) : d356704 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d39767, d356704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39767, d356704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d39768 q = 1) (hb : d46864 q = 1) : d356705 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d39768, d356705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39768, d356705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d39769 q = 1) (hb : d46864 q = 1) : d356706 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d39769, d356706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39769, d356706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d46864 q = 1) (hb : d333402 q = 1) : d357050 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d333402, d357050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d333402, d357050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro96954 (p : Pattern) (ha : d46864 p = 1) (hb : d333413 p = 1) : d357061 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46864 q = 1) (hb : d333408 q = 1) : d357056 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d333408, d357056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96403 q hb ha
    | true =>
      simp only [d333408, d357056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96371 q hb ha
  have h2 (q : Pattern) (ha : d46864 q = 1) (hb : d333409 q = 1) : d357057 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d333409, d357057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d333409, d357057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d46864 q = 1) (hb : d333410 q = 1) : d357058 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d333410, d357058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d333410, d357058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d46864 q = 1) (hb : d333411 q = 1) : d357059 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d333411, d357059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d333411, d357059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d46864 q = 1) (hb : d333412 q = 1) : d357060 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d333412, d357060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d333412, d357060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d46864 q = 1) (hb : d333413 q = 1) : d357061 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d333413, d357061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d333413, d357061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro96955 (p : Pattern) (ha : d46864 p = 1) (hb : d333419 p = 1) : d357067 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d39771 q = 1) (hb : d46864 q = 1) : d356708 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d39771, d356708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96361 q ha hb
    | true =>
      simp only [d39771, d356708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96364 q ha hb
  have h2 (q : Pattern) (ha : d39772 q = 1) (hb : d46864 q = 1) : d356709 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d39772, d356709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d39772, d356709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d46864 q = 1) (hb : d333400 q = 1) : d357048 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d333400, d357048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d333400, d357048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d46864 q = 1) (hb : d333401 q = 1) : d357049 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d333401, d357049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d333401, d357049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d46864 q = 1) (hb : d333403 q = 1) : d357051 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d333403, d357051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d333403, d357051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96953 q ha hb
  have h6 (q : Pattern) (ha : d46864 q = 1) (hb : d333404 q = 1) : d357052 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d333404, d357052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d333404, d357052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d46864 q = 1) (hb : d333405 q = 1) : d357053 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d333405, d357053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d333405, d357053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d46864 q = 1) (hb : d333406 q = 1) : d357054 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d333406, d357054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d333406, d357054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d46864 q = 1) (hb : d333407 q = 1) : d357055 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d333407, d357055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d333407, d357055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d46864 q = 1) (hb : d333414 q = 1) : d357062 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d333414, d357062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d333414, d357062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96954 q ha hb
  have h11 (q : Pattern) (ha : d46864 q = 1) (hb : d333415 q = 1) : d357063 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d333415, d357063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d333415, d357063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d46864 q = 1) (hb : d333416 q = 1) : d357064 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d333416, d357064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d333416, d357064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d46864 q = 1) (hb : d333417 q = 1) : d357065 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d333417, d357065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d333417, d357065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d46864 q = 1) (hb : d333418 q = 1) : d357066 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d333418, d357066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d333418, d357066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d46864 q = 1) (hb : d333419 q = 1) : d357067 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d333419, d357067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d333419, d357067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro96956 (p : Pattern) (ha : d46864 p = 1) (hb : d333425 p = 1) : d357073 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46864 q = 1) (hb : d333420 q = 1) : d357068 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d333420, d357068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d333420, d357068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96955 q ha hb
  have h2 (q : Pattern) (ha : d46864 q = 1) (hb : d333421 q = 1) : d357069 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d333421, d357069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d333421, d357069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d46864 q = 1) (hb : d333422 q = 1) : d357070 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d333422, d357070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d333422, d357070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d46864 q = 1) (hb : d333423 q = 1) : d357071 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d333423, d357071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d333423, d357071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d46864 q = 1) (hb : d333424 q = 1) : d357072 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d333424, d357072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d333424, d357072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d46864 q = 1) (hb : d333425 q = 1) : d357073 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d333425, d357073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d333425, d357073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro96957 (p : Pattern) (ha : d46864 p = 1) (hb : d338550 p = 1) : d357020 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d41239 q = 1) (hb : d46864 q = 1) : d356432 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d41239, d356432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96591 q ha hb
    | true =>
      simp only [d41239, d356432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96592 q ha hb
  have h2 (q : Pattern) (ha : d41240 q = 1) (hb : d46864 q = 1) : d356433 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d41240, d356433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d41240, d356433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d41241 q = 1) (hb : d46864 q = 1) : d356434 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d41241, d356434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d41241, d356434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d41242 q = 1) (hb : d46864 q = 1) : d356435 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d41242, d356435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d41242, d356435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d41243 q = 1) (hb : d46864 q = 1) : d356436 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d41243, d356436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d41243, d356436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d46864 q = 1) (hb : d338550 q = 1) : d357020 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d338550, d357020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d338550, d357020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro96958 (p : Pattern) (ha : d46864 p = 1) (hb : d338561 p = 1) : d357031 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46864 q = 1) (hb : d338556 q = 1) : d357026 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d338556, d357026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96631 q hb ha
    | true =>
      simp only [d338556, d357026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96600 q hb ha
  have h2 (q : Pattern) (ha : d46864 q = 1) (hb : d338557 q = 1) : d357027 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d338557, d357027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d338557, d357027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d46864 q = 1) (hb : d338558 q = 1) : d357028 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d338558, d357028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d338558, d357028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d46864 q = 1) (hb : d338559 q = 1) : d357029 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d338559, d357029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d338559, d357029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d46864 q = 1) (hb : d338560 q = 1) : d357030 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d338560, d357030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d338560, d357030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d46864 q = 1) (hb : d338561 q = 1) : d357031 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d338561, d357031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d338561, d357031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro96959 (p : Pattern) (ha : d46864 p = 1) (hb : d338567 p = 1) : d357037 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d41245 q = 1) (hb : d46864 q = 1) : d356438 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d41245, d356438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96590 q ha hb
    | true =>
      simp only [d41245, d356438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96593 q ha hb
  have h2 (q : Pattern) (ha : d41246 q = 1) (hb : d46864 q = 1) : d356439 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d41246, d356439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d41246, d356439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d46864 q = 1) (hb : d338548 q = 1) : d357018 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d338548, d357018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d338548, d357018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d46864 q = 1) (hb : d338549 q = 1) : d357019 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d338549, d357019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d338549, d357019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d46864 q = 1) (hb : d338551 q = 1) : d357021 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d338551, d357021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d338551, d357021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96957 q ha hb
  have h6 (q : Pattern) (ha : d46864 q = 1) (hb : d338552 q = 1) : d357022 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d338552, d357022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d338552, d357022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d46864 q = 1) (hb : d338553 q = 1) : d357023 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d338553, d357023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d338553, d357023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d46864 q = 1) (hb : d338554 q = 1) : d357024 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d338554, d357024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d338554, d357024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d46864 q = 1) (hb : d338555 q = 1) : d357025 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d338555, d357025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d338555, d357025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d46864 q = 1) (hb : d338562 q = 1) : d357032 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d338562, d357032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d338562, d357032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96958 q ha hb
  have h11 (q : Pattern) (ha : d46864 q = 1) (hb : d338563 q = 1) : d357033 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d338563, d357033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d338563, d357033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d46864 q = 1) (hb : d338564 q = 1) : d357034 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d338564, d357034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d338564, d357034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d46864 q = 1) (hb : d338565 q = 1) : d357035 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d338565, d357035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d338565, d357035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d46864 q = 1) (hb : d338566 q = 1) : d357036 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d338566, d357036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d338566, d357036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d46864 q = 1) (hb : d338567 q = 1) : d357037 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d338567, d357037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d338567, d357037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro96960 (p : Pattern) (ha : d46864 p = 1) (hb : d338573 p = 1) : d357043 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46864 q = 1) (hb : d338568 q = 1) : d357038 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d338568, d357038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d338568, d357038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96959 q ha hb
  have h2 (q : Pattern) (ha : d46864 q = 1) (hb : d338569 q = 1) : d357039 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d338569, d357039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d338569, d357039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d46864 q = 1) (hb : d338570 q = 1) : d357040 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d338570, d357040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d338570, d357040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d46864 q = 1) (hb : d338571 q = 1) : d357041 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d338571, d357041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d338571, d357041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d46864 q = 1) (hb : d338572 q = 1) : d357042 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d338572, d357042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d338572, d357042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d46864 q = 1) (hb : d338573 q = 1) : d357043 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d338573, d357043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d338573, d357043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro96961 (p : Pattern) (ha : d46864 p = 1) (hb : d338579 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d41766 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d41766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96659 q ha hb
    | true =>
      simp only [d41766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96660 q ha hb
  have h2 (q : Pattern) (ha : d41767 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d41767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d41767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d41768 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d41768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d41768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d41769 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d41769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d41769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d41770 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d41770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d41770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d46864 q = 1) (hb : d338579 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d338579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d338579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro96962 (p : Pattern) (ha : d46864 p = 1) (hb : d338590 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46864 q = 1) (hb : d338585 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d338585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96701 q hb ha
    | true =>
      simp only [d338585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96668 q hb ha
  have h2 (q : Pattern) (ha : d46864 q = 1) (hb : d338586 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d338586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d338586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d46864 q = 1) (hb : d338587 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d338587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d338587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d46864 q = 1) (hb : d338588 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d338588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d338588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d46864 q = 1) (hb : d338589 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d338589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d338589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d46864 q = 1) (hb : d338590 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d338590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d338590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro96963 (p : Pattern) (ha : d46864 p = 1) (hb : d338596 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d41772 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d41772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96658 q ha hb
    | true =>
      simp only [d41772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96661 q ha hb
  have h2 (q : Pattern) (ha : d41773 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d41773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d41773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d46864 q = 1) (hb : d338577 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d338577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d338577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d46864 q = 1) (hb : d338578 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d338578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d338578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d46864 q = 1) (hb : d338580 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d338580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d338580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96961 q ha hb
  have h6 (q : Pattern) (ha : d46864 q = 1) (hb : d338581 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d338581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d338581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d46864 q = 1) (hb : d338582 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d338582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d338582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d46864 q = 1) (hb : d338583 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d338583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d338583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d46864 q = 1) (hb : d338584 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d338584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d338584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d46864 q = 1) (hb : d338591 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d338591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d338591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96962 q ha hb
  have h11 (q : Pattern) (ha : d46864 q = 1) (hb : d338592 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d338592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d338592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d46864 q = 1) (hb : d338593 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d338593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d338593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d46864 q = 1) (hb : d338594 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d338594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d338594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d46864 q = 1) (hb : d338595 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d338595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d338595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d46864 q = 1) (hb : d338596 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d338596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d338596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro96964 (p : Pattern) (ha : d46864 p = 1) (hb : d338602 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46864 q = 1) (hb : d338597 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d338597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d338597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96963 q ha hb
  have h2 (q : Pattern) (ha : d46864 q = 1) (hb : d338598 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d338598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d338598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d46864 q = 1) (hb : d338599 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d338599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d338599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d46864 q = 1) (hb : d338600 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d338600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d338600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d46864 q = 1) (hb : d338601 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d338601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d338601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d46864 q = 1) (hb : d338602 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d338602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d338602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro96965 (p : Pattern) (ha : d46864 p = 1) (hb : d338608 p = 1) : d357079 p = 1 := by
  have h0 (q : Pattern) (ha : d46864 q = 1) (hb : d290115 q = 1) : d356989 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d290115, d356989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96944 q ha hb
    | true =>
      simp only [d290115, d356989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96948 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d46864 q = 1) (hb : d290142 q = 1) : d357016 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d290142, d357016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d290142, d357016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96952 q ha hb
  have h3 (q : Pattern) (ha : d46864 q = 1) (hb : d290143 q = 1) : d357017 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d290143, d357017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d290143, d357017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d46864 q = 1) (hb : d338574 q = 1) : d357044 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d338574, d357044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d338574, d357044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96960 q ha hb
  have h5 (q : Pattern) (ha : d46864 q = 1) (hb : d338575 q = 1) : d357045 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d338575, d357045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d338575, d357045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d46864 q = 1) (hb : d338576 q = 1) : d357046 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d338576, d357046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d338576, d357046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d46864 q = 1) (hb : d338603 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d338603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d338603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96964 q ha hb
  have h8 (q : Pattern) (ha : d46864 q = 1) (hb : d338604 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d338604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d338604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d46864 q = 1) (hb : d338605 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d338605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d338605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d46864 q = 1) (hb : d338606 q = 1) : d357047 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d338606, d357047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d338606, d357047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d46864 q = 1) (hb : d333426 q = 1) : d357074 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d333426, d357074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d333426, d357074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96956 q ha hb
  have h12 (q : Pattern) (ha : d46864 q = 1) (hb : d333427 q = 1) : d357075 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d333427, d357075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d333427, d357075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d46864 q = 1) (hb : d333428 q = 1) : d357076 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d333428, d357076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d333428, d357076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d46864 q = 1) (hb : d333429 q = 1) : d357077 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d333429, d357077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d333429, d357077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d46864 q = 1) (hb : d338607 q = 1) : d357078 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d338607, d357078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d338607, d357078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d46864 q = 1) (hb : d338608 q = 1) : d357079 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d338608, d357079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d338608, d357079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro96966 (p : Pattern) (ha : d46864 p = 1) (hb : d338614 p = 1) : d357085 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46864 q = 1) (hb : d338609 q = 1) : d357080 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d338609, d357080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96965 q ha hb
    | true =>
      simp only [d338609, d357080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d46864 q = 1) (hb : d338610 q = 1) : d357081 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d338610, d357081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d338610, d357081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d46864 q = 1) (hb : d338611 q = 1) : d357082 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d338611, d357082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d338611, d357082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d46864 q = 1) (hb : d338612 q = 1) : d357083 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d338612, d357083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d338612, d357083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d46864 q = 1) (hb : d338613 q = 1) : d357084 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d338613, d357084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d338613, d357084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d46864 q = 1) (hb : d338614 q = 1) : d357085 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d338614, d357085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d338614, d357085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro96967 (p : Pattern) (ha : d46864 p = 1) (hb : d338620 p = 1) : d357091 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46864 q = 1) (hb : d338615 q = 1) : d357086 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d338615, d357086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96966 q ha hb
    | true =>
      simp only [d338615, d357086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d46864 q = 1) (hb : d338616 q = 1) : d357087 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d338616, d357087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d338616, d357087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d46864 q = 1) (hb : d338617 q = 1) : d357088 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d338617, d357088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d338617, d357088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d46864 q = 1) (hb : d338618 q = 1) : d357089 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d338618, d357089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d338618, d357089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d46864 q = 1) (hb : d338619 q = 1) : d357090 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d338619, d357090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d338619, d357090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d46864 q = 1) (hb : d338620 q = 1) : d357091 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d338620, d357091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d338620, d357091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro96968 (p : Pattern) (ha : d46864 p = 1) (hb : d338626 p = 1) : d357097 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46864 q = 1) (hb : d338621 q = 1) : d357092 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d338621, d357092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96967 q ha hb
    | true =>
      simp only [d338621, d357092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d46864 q = 1) (hb : d338622 q = 1) : d357093 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d338622, d357093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d338622, d357093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d46864 q = 1) (hb : d338623 q = 1) : d357094 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d338623, d357094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d338623, d357094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d46864 q = 1) (hb : d338624 q = 1) : d357095 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d338624, d357095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d338624, d357095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d46864 q = 1) (hb : d338625 q = 1) : d357096 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d338625, d357096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d338625, d357096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d46864 q = 1) (hb : d338626 q = 1) : d357097 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d338626, d357097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d338626, d357097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro96969 (p : Pattern) (ha : d46864 p = 1) (hb : d338632 p = 1) : d357103 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46864 q = 1) (hb : d338627 q = 1) : d357098 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d338627, d357098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96968 q ha hb
    | true =>
      simp only [d338627, d357098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d46864 q = 1) (hb : d338628 q = 1) : d357099 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d338628, d357099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d338628, d357099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d46864 q = 1) (hb : d338629 q = 1) : d357100 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d338629, d357100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d338629, d357100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d46864 q = 1) (hb : d338630 q = 1) : d357101 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d338630, d357101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d338630, d357101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d46864 q = 1) (hb : d338631 q = 1) : d357102 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d338631, d357102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d338631, d357102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d46864 q = 1) (hb : d338632 q = 1) : d357103 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d338632, d357103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d338632, d357103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro96970 (p : Pattern) (ha : d46864 p = 1) (hb : d338638 p = 1) : d357109 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46864 q = 1) (hb : d338633 q = 1) : d357104 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d338633, d357104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96969 q ha hb
    | true =>
      simp only [d338633, d357104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d46864 q = 1) (hb : d338634 q = 1) : d357105 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d338634, d357105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d338634, d357105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d46864 q = 1) (hb : d338635 q = 1) : d357106 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d338635, d357106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d338635, d357106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d46864 q = 1) (hb : d338636 q = 1) : d357107 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d338636, d357107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d338636, d357107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d46864 q = 1) (hb : d338637 q = 1) : d357108 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d338637, d357108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d338637, d357108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d46864 q = 1) (hb : d338638 q = 1) : d357109 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d338638, d357109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d338638, d357109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro96971 (p : Pattern) (ha : d46864 p = 1) (hb : d338644 p = 1) : d357115 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46864 q = 1) (hb : d338639 q = 1) : d357110 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d338639, d357110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96970 q ha hb
    | true =>
      simp only [d338639, d357110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d46864 q = 1) (hb : d338640 q = 1) : d357111 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d338640, d357111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d338640, d357111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d46864 q = 1) (hb : d338641 q = 1) : d357112 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d338641, d357112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d338641, d357112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d46864 q = 1) (hb : d338642 q = 1) : d357113 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d338642, d357113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d338642, d357113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d46864 q = 1) (hb : d338643 q = 1) : d357114 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d338643, d357114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d338643, d357114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d46864 q = 1) (hb : d338644 q = 1) : d357115 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d338644, d357115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d338644, d357115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro96972 (p : Pattern) (ha : d46864 p = 1) (hb : d338650 p = 1) : d357121 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46864 q = 1) (hb : d338645 q = 1) : d357116 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d338645, d357116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96971 q ha hb
    | true =>
      simp only [d338645, d357116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d46864 q = 1) (hb : d338646 q = 1) : d357117 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d338646, d357117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d338646, d357117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d46864 q = 1) (hb : d338647 q = 1) : d357118 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d338647, d357118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d338647, d357118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d46864 q = 1) (hb : d338648 q = 1) : d357119 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d338648, d357119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d338648, d357119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d46864 q = 1) (hb : d338649 q = 1) : d357120 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d338649, d357120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d338649, d357120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d46864 q = 1) (hb : d338650 q = 1) : d357121 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d338650, d357121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d338650, d357121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro96973 (p : Pattern) (ha : d354277 p = 1) (hb : d355861 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d354238 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d354244 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d354272 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d354160 q = 1) (hb : d355799 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d354160, d355799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96721 q ha hb
    | true =>
      simp only [d354160, d355799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d354273 q = 1) (hb : d355857 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d354273, d355857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d354273, d355857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d354161 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d354274 q = 1) (hb : d355858 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d354274, d355858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d354274, d355858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d354275 q = 1) (hb : d355859 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d354275, d355859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d354275, d355859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d354276 q = 1) (hb : d355860 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d354276, d355860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d354276, d355860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d354277 q = 1) (hb : d355861 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d354277, d355861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354277, d355861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro96974 (p : Pattern) (ha : d354293 p = 1) (hb : d355868 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d354238 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d354244 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d354272 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d354160 q = 1) (hb : d355799 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d354160, d355799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96721 q ha hb
    | true =>
      simp only [d354160, d355799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d354273 q = 1) (hb : d355857 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d354273, d355857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d354273, d355857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d354161 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d354274 q = 1) (hb : d355858 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d354274, d355858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d354274, d355858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d354275 q = 1) (hb : d355859 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d354275, d355859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d354275, d355859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d354276 q = 1) (hb : d355860 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d354276, d355860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354276, d355860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d354282 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d354286 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d354288 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d354167 q = 1) (hb : d355806 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d354167, d355806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96723 q ha hb
    | true =>
      simp only [d354167, d355806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h14 (q : Pattern) (ha : d354289 q = 1) (hb : d355864 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d354289, d355864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
    | true =>
      simp only [d354289, d355864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d354168 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d354290 q = 1) (hb : d355865 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d354290, d355865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d354290, d355865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
  have h17 (q : Pattern) (ha : d354291 q = 1) (hb : d355866 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d354291, d355866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d354291, d355866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d354292 q = 1) (hb : d355867 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d354292, d355867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d354292, d355867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d354293 q = 1) (hb : d355868 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d354293, d355868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d354293, d355868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro96975 (p : Pattern) (ha : d354302 p = 1) (hb : d356088 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d354288 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d354167 q = 1) (hb : d355806 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d354167, d355806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96723 q ha hb
    | true =>
      simp only [d354167, d355806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d354289 q = 1) (hb : d355864 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d354289, d355864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d354289, d355864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d354168 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d354290 q = 1) (hb : d355865 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d354290, d355865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d354290, d355865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d354300 q = 1) (hb : d355866 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d354300, d355866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354300, d355866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d354301 q = 1) (hb : d355867 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d354301, d355867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354301, d355867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d354302 q = 1) (hb : d356088 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d354302, d356088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354302, d356088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro96976 (p : Pattern) (ha : d354331 p = 1) (hb : d356134 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d354326 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d354201 q = 1) (hb : d355840 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d354201, d355840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96728 q ha hb
    | true =>
      simp only [d354201, d355840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d354327 q = 1) (hb : d356130 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d354327, d356130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d354327, d356130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d354202 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d354328 q = 1) (hb : d356131 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d354328, d356131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d354328, d356131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d354329 q = 1) (hb : d356132 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d354329, d356132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354329, d356132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d354330 q = 1) (hb : d356133 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d354330, d356133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354330, d356133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d354331 q = 1) (hb : d356134 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d354331, d356134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354331, d356134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro96977 (p : Pattern) (ha : d354337 p = 1) (hb : d356957 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d354232 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d354294 q = 1) (hb : d355869 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d354294, d355869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96973 q ha hb
    | true =>
      simp only [d354294, d355869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96974 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d354296 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d354297 q = 1) (hb : d355870 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d354297, d355870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d354297, d355870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d354298 q = 1) (hb : d356947 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d354298, d356947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d354298, d356947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d354299 q = 1) (hb : d356948 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d354299, d356948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354299, d356948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d354303 q = 1) (hb : d356089 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d354303, d356089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d354303, d356089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96975 q ha hb
  have h8 (q : Pattern) (ha : d354304 q = 1) (hb : d356949 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d354304, d356949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d354304, d356949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h9 (q : Pattern) (ha : d354305 q = 1) (hb : d356950 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d354305, d356950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d354305, d356950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h10 (q : Pattern) (ha : d354306 q = 1) (hb : d356951 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d354306, d356951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d354306, d356951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d354307 q = 1) (hb : d356952 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d354307, d356952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d354307, d356952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d354332 q = 1) (hb : d356135 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d354332, d356135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d354332, d356135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96976 q ha hb
  have h13 (q : Pattern) (ha : d354333 q = 1) (hb : d356953 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d354333, d356953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d354333, d356953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h14 (q : Pattern) (ha : d354334 q = 1) (hb : d356954 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d354334, d356954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d354334, d356954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h15 (q : Pattern) (ha : d354335 q = 1) (hb : d356955 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d354335, d356955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d354335, d356955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h16 (q : Pattern) (ha : d354336 q = 1) (hb : d356956 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d354336, d356956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d354336, d356956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d354337 q = 1) (hb : d356957 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d354337, d356957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d354337, d356957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro96978 (p : Pattern) (ha : d354343 p = 1) (hb : d356963 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d354217 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d354338 q = 1) (hb : d356958 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d354338, d356958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d354338, d356958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96977 q ha hb
  have h3 (q : Pattern) (ha : d354339 q = 1) (hb : d356959 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d354339, d356959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d354339, d356959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d354340 q = 1) (hb : d356960 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d354340, d356960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d354340, d356960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d354341 q = 1) (hb : d356961 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d354341, d356961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d354341, d356961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d354342 q = 1) (hb : d356962 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d354342, d356962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d354342, d356962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d354343 q = 1) (hb : d356963 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d354343, d356963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354343, d356963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro96979 (p : Pattern) (ha : d354418 p = 1) (hb : d355986 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d354364 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d354370 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d354407 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d354272 q = 1) (hb : d355910 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d354272, d355910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96739 q ha hb
    | true =>
      simp only [d354272, d355910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96721 q ha hb
  have h5 (q : Pattern) (ha : d354408 q = 1) (hb : d355982 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d354408, d355982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d354408, d355982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d354414 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d354415 q = 1) (hb : d355983 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d354415, d355983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d354415, d355983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d354416 q = 1) (hb : d355984 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d354416, d355984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d354416, d355984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d354417 q = 1) (hb : d355985 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d354417, d355985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d354417, d355985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d354418 q = 1) (hb : d355986 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d354418, d355986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354418, d355986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro96980 (p : Pattern) (ha : d354437 p = 1) (hb : d355993 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d354364 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d354370 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d354407 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d354272 q = 1) (hb : d355910 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d354272, d355910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96739 q ha hb
    | true =>
      simp only [d354272, d355910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96721 q ha hb
  have h4 (q : Pattern) (ha : d354408 q = 1) (hb : d355982 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d354408, d355982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d354408, d355982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d354414 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d354415 q = 1) (hb : d355983 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d354415, d355983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d354415, d355983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d354416 q = 1) (hb : d355984 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d354416, d355984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d354416, d355984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d354417 q = 1) (hb : d355985 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d354417, d355985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354417, d355985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d354423 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d354427 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d354429 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d354288 q = 1) (hb : d355926 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d354288, d355926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96743 q ha hb
    | true =>
      simp only [d354288, d355926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96723 q ha hb
  have h13 (q : Pattern) (ha : d354430 q = 1) (hb : d355989 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d354430, d355989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d354430, d355989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d354433 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d354434 q = 1) (hb : d355990 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d354434, d355990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d354434, d355990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d354435 q = 1) (hb : d355991 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d354435, d355991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d354435, d355991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d354436 q = 1) (hb : d355992 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d354436, d355992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d354436, d355992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d354437 q = 1) (hb : d355993 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d354437, d355993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d354437, d355993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro96981 (p : Pattern) (ha : d354446 p = 1) (hb : d356966 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d354429 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d354288 q = 1) (hb : d355926 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d354288, d355926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96743 q ha hb
    | true =>
      simp only [d354288, d355926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96723 q ha hb
  have h3 (q : Pattern) (ha : d354430 q = 1) (hb : d355989 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d354430, d355989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d354430, d355989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d354433 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d354434 q = 1) (hb : d355990 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d354434, d355990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d354434, d355990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d354444 q = 1) (hb : d355991 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d354444, d355991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354444, d355991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d354445 q = 1) (hb : d355992 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d354445, d355992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354445, d355992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d354446 q = 1) (hb : d356966 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d354446, d356966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354446, d356966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro96982 (p : Pattern) (ha : d354488 p = 1) (hb : d356976 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d354477 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d354326 q = 1) (hb : d355964 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d354326, d355964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96749 q ha hb
    | true =>
      simp only [d354326, d355964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96728 q ha hb
  have h3 (q : Pattern) (ha : d354478 q = 1) (hb : d356972 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d354478, d356972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d354478, d356972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d354484 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d354485 q = 1) (hb : d356973 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d354485, d356973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d354485, d356973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d354486 q = 1) (hb : d356974 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d354486, d356974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354486, d356974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d354487 q = 1) (hb : d356975 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d354487, d356975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354487, d356975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d354488 q = 1) (hb : d356976 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d354488, d356976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354488, d356976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro96983 (p : Pattern) (ha : d354500 p = 1) (hb : d356982 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d354358 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d354438 q = 1) (hb : d355994 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d354438, d355994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96979 q ha hb
    | true =>
      simp only [d354438, d355994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96980 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d354440 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d354441 q = 1) (hb : d355995 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d354441, d355995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d354441, d355995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d354442 q = 1) (hb : d356964 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d354442, d356964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d354442, d356964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d354443 q = 1) (hb : d356965 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d354443, d356965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354443, d356965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d354447 q = 1) (hb : d356967 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d354447, d356967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d354447, d356967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96981 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d354449 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d354450 q = 1) (hb : d356968 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d354450, d356968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d354450, d356968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d354451 q = 1) (hb : d356969 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d354451, d356969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d354451, d356969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d354452 q = 1) (hb : d356970 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d354452, d356970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d354452, d356970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d354453 q = 1) (hb : d356971 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d354453, d356971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d354453, d356971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d354489 q = 1) (hb : d356977 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d354489, d356977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d354489, d356977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96982 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d354495 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d354496 q = 1) (hb : d356978 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d354496, d356978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d354496, d356978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d354497 q = 1) (hb : d356979 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d354497, d356979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d354497, d356979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d354498 q = 1) (hb : d356980 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d354498, d356980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d354498, d356980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d354499 q = 1) (hb : d356981 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d354499, d356981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d354499, d356981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d354500 q = 1) (hb : d356982 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d354500, d356982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d354500, d356982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro96984 (p : Pattern) (ha : d354506 p = 1) (hb : d356988 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d354501 q = 1) (hb : d356983 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d354501, d356983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354501, d356983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96983 q ha hb
  have h2 (q : Pattern) (ha : d354502 q = 1) (hb : d356984 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d354502, d356984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354502, d356984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d354503 q = 1) (hb : d356985 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d354503, d356985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354503, d356985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d354504 q = 1) (hb : d356986 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d354504, d356986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354504, d356986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d354505 q = 1) (hb : d356987 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d354505, d356987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354505, d356987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d354506 q = 1) (hb : d356988 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d354506, d356988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354506, d356988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro96985 (p : Pattern) (ha : d354622 p = 1) (hb : d356170 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d354551 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d354560 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d354611 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d354525 q = 1) (hb : d356165 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d354525, d356165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96784 q ha hb
    | true =>
      simp only [d354525, d356165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96785 q ha hb
  have h5 (q : Pattern) (ha : d354612 q = 1) (hb : d356166 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d354612, d356166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d354612, d356166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d354618 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d354619 q = 1) (hb : d356167 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d354619, d356167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d354619, d356167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d354620 q = 1) (hb : d356168 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d354620, d356168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d354620, d356168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d354621 q = 1) (hb : d356169 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d354621, d356169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d354621, d356169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d354622 q = 1) (hb : d356170 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d354622, d356170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354622, d356170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro96986 (p : Pattern) (ha : d354643 p = 1) (hb : d356180 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d354551 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d354560 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d354611 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d354525 q = 1) (hb : d356165 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d354525, d356165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96784 q ha hb
    | true =>
      simp only [d354525, d356165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96785 q ha hb
  have h4 (q : Pattern) (ha : d354612 q = 1) (hb : d356166 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d354612, d356166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d354612, d356166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d354618 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d354619 q = 1) (hb : d356167 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d354619, d356167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d354619, d356167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d354620 q = 1) (hb : d356168 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d354620, d356168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d354620, d356168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d354621 q = 1) (hb : d356169 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d354621, d356169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354621, d356169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d354628 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d354633 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d354635 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d354535 q = 1) (hb : d356175 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d354535, d356175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96787 q ha hb
    | true =>
      simp only [d354535, d356175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96788 q ha hb
  have h13 (q : Pattern) (ha : d354636 q = 1) (hb : d356176 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d354636, d356176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d354636, d356176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d354639 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d354640 q = 1) (hb : d356177 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d354640, d356177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d354640, d356177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d354641 q = 1) (hb : d356178 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d354641, d356178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d354641, d356178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d354642 q = 1) (hb : d356179 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d354642, d356179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d354642, d356179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d354643 q = 1) (hb : d356180 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d354643, d356180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d354643, d356180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro96987 (p : Pattern) (ha : d354663 p = 1) (hb : d356992 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d354635 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d354535 q = 1) (hb : d356175 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d354535, d356175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96787 q ha hb
    | true =>
      simp only [d354535, d356175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96788 q ha hb
  have h3 (q : Pattern) (ha : d354636 q = 1) (hb : d356176 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d354636, d356176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d354636, d356176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d354639 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d354640 q = 1) (hb : d356177 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d354640, d356177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d354640, d356177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d354661 q = 1) (hb : d356178 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d354661, d356178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354661, d356178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d354662 q = 1) (hb : d356179 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d354662, d356179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354662, d356179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d354663 q = 1) (hb : d356992 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d354663, d356992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354663, d356992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro96988 (p : Pattern) (ha : d354731 p = 1) (hb : d357003 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d354715 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d354720 q = 1) (hb : d356998 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d354720, d356998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96821 q ha hb
    | true =>
      simp only [d354720, d356998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96824 q ha hb
  have h3 (q : Pattern) (ha : d354721 q = 1) (hb : d356999 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d354721, d356999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d354721, d356999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d354727 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d354728 q = 1) (hb : d357000 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d354728, d357000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d354728, d357000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d354729 q = 1) (hb : d357001 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d354729, d357001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354729, d357001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d354730 q = 1) (hb : d357002 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d354730, d357002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354730, d357002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d354731 q = 1) (hb : d357003 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d354731, d357003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354731, d357003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro96989 (p : Pattern) (ha : d354744 p = 1) (hb : d357009 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d354543 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d354644 q = 1) (hb : d356181 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d354644, d356181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96985 q ha hb
    | true =>
      simp only [d354644, d356181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96986 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d354657 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d354658 q = 1) (hb : d356182 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d354658, d356182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d354658, d356182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d354659 q = 1) (hb : d356990 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d354659, d356990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d354659, d356990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d354660 q = 1) (hb : d356991 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d354660, d356991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354660, d356991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d354664 q = 1) (hb : d356993 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d354664, d356993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d354664, d356993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96987 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d354666 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d354667 q = 1) (hb : d356994 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d354667, d356994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d354667, d356994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d354668 q = 1) (hb : d356995 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d354668, d356995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d354668, d356995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d354669 q = 1) (hb : d356996 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d354669, d356996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d354669, d356996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d354670 q = 1) (hb : d356997 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d354670, d356997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d354670, d356997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d354732 q = 1) (hb : d357004 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d354732, d357004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d354732, d357004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96988 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d354739 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d354740 q = 1) (hb : d357005 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d354740, d357005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d354740, d357005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d354741 q = 1) (hb : d357006 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d354741, d357006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d354741, d357006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d354742 q = 1) (hb : d357007 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d354742, d357007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d354742, d357007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d354743 q = 1) (hb : d357008 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d354743, d357008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d354743, d357008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d354744 q = 1) (hb : d357009 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d354744, d357009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d354744, d357009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro96990 (p : Pattern) (ha : d354750 p = 1) (hb : d357015 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d354745 q = 1) (hb : d357010 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d354745, d357010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354745, d357010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96989 q ha hb
  have h2 (q : Pattern) (ha : d354746 q = 1) (hb : d357011 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d354746, d357011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354746, d357011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d354747 q = 1) (hb : d357012 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d354747, d357012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354747, d357012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d354748 q = 1) (hb : d357013 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d354748, d357013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354748, d357013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d354749 q = 1) (hb : d357014 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d354749, d357014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354749, d357014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d354750 q = 1) (hb : d357015 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d354750, d357015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354750, d357015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro96991 (p : Pattern) (ha : d354889 p = 1) (hb : d356427 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d354814 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d354823 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d354878 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d354788 q = 1) (hb : d356422 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d354788, d356422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96834 q ha hb
    | true =>
      simp only [d354788, d356422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96835 q ha hb
  have h5 (q : Pattern) (ha : d354879 q = 1) (hb : d356423 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d354879, d356423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d354879, d356423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d354885 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d354886 q = 1) (hb : d356424 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d354886, d356424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d354886, d356424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d354887 q = 1) (hb : d356425 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d354887, d356425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d354887, d356425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d354888 q = 1) (hb : d356426 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d354888, d356426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d354888, d356426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d354889 q = 1) (hb : d356427 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d354889, d356427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354889, d356427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro96992 (p : Pattern) (ha : d354910 p = 1) (hb : d356437 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d354814 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d354823 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d354878 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d354788 q = 1) (hb : d356422 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d354788, d356422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96834 q ha hb
    | true =>
      simp only [d354788, d356422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96835 q ha hb
  have h4 (q : Pattern) (ha : d354879 q = 1) (hb : d356423 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d354879, d356423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d354879, d356423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d354885 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d354886 q = 1) (hb : d356424 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d354886, d356424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d354886, d356424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d354887 q = 1) (hb : d356425 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d354887, d356425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d354887, d356425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d354888 q = 1) (hb : d356426 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d354888, d356426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354888, d356426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d354895 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d354900 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d354902 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d354798 q = 1) (hb : d356432 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d354798, d356432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96837 q ha hb
    | true =>
      simp only [d354798, d356432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96838 q ha hb
  have h13 (q : Pattern) (ha : d354903 q = 1) (hb : d356433 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d354903, d356433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d354903, d356433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d354906 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d354907 q = 1) (hb : d356434 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d354907, d356434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d354907, d356434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d354908 q = 1) (hb : d356435 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d354908, d356435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d354908, d356435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d354909 q = 1) (hb : d356436 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d354909, d356436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d354909, d356436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d354910 q = 1) (hb : d356437 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d354910, d356437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d354910, d356437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro96993 (p : Pattern) (ha : d354930 p = 1) (hb : d357020 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d354902 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d354798 q = 1) (hb : d356432 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d354798, d356432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96837 q ha hb
    | true =>
      simp only [d354798, d356432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96838 q ha hb
  have h3 (q : Pattern) (ha : d354903 q = 1) (hb : d356433 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d354903, d356433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d354903, d356433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d354906 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d354907 q = 1) (hb : d356434 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d354907, d356434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d354907, d356434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d354928 q = 1) (hb : d356435 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d354928, d356435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354928, d356435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d354929 q = 1) (hb : d356436 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d354929, d356436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354929, d356436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d354930 q = 1) (hb : d357020 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d354930, d357020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354930, d357020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro96994 (p : Pattern) (ha : d355015 p = 1) (hb : d357031 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d354999 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d355004 q = 1) (hb : d357026 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d355004, d357026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96874 q ha hb
    | true =>
      simp only [d355004, d357026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96877 q ha hb
  have h3 (q : Pattern) (ha : d355005 q = 1) (hb : d357027 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d355005, d357027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d355005, d357027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d355011 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d355012 q = 1) (hb : d357028 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d355012, d357028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d355012, d357028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d355013 q = 1) (hb : d357029 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d355013, d357029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d355013, d357029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d355014 q = 1) (hb : d357030 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d355014, d357030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d355014, d357030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d355015 q = 1) (hb : d357031 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d355015, d357031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d355015, d357031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro96995 (p : Pattern) (ha : d355028 p = 1) (hb : d357037 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d354806 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d354911 q = 1) (hb : d356438 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d354911, d356438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96991 q ha hb
    | true =>
      simp only [d354911, d356438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96992 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d354924 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d354925 q = 1) (hb : d356439 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d354925, d356439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d354925, d356439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d354926 q = 1) (hb : d357018 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d354926, d357018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d354926, d357018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d354927 q = 1) (hb : d357019 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d354927, d357019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d354927, d357019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d354931 q = 1) (hb : d357021 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d354931, d357021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d354931, d357021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96993 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d354933 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d354934 q = 1) (hb : d357022 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d354934, d357022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d354934, d357022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d354935 q = 1) (hb : d357023 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d354935, d357023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d354935, d357023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d354936 q = 1) (hb : d357024 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d354936, d357024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d354936, d357024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d354937 q = 1) (hb : d357025 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d354937, d357025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d354937, d357025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d355016 q = 1) (hb : d357032 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d355016, d357032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d355016, d357032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96994 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d355023 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d355024 q = 1) (hb : d357033 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d355024, d357033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d355024, d357033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d355025 q = 1) (hb : d357034 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d355025, d357034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d355025, d357034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d355026 q = 1) (hb : d357035 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d355026, d357035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d355026, d357035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d355027 q = 1) (hb : d357036 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d355027, d357036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d355027, d357036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d355028 q = 1) (hb : d357037 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d355028, d357037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d355028, d357037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro96996 (p : Pattern) (ha : d355034 p = 1) (hb : d357043 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d355029 q = 1) (hb : d357038 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d355029, d357038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d355029, d357038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96995 q ha hb
  have h2 (q : Pattern) (ha : d355030 q = 1) (hb : d357039 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d355030, d357039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d355030, d357039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d355031 q = 1) (hb : d357040 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d355031, d357040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d355031, d357040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d355032 q = 1) (hb : d357041 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d355032, d357041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d355032, d357041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d355033 q = 1) (hb : d357042 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d355033, d357042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d355033, d357042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d355034 q = 1) (hb : d357043 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d355034, d357043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d355034, d357043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro96997 (p : Pattern) (ha : d355576 p = 1) (hb : d356697 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d355526 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d355535 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d355549 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d355500 q = 1) (hb : d356692 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d355500, d356692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96889 q ha hb
    | true =>
      simp only [d355500, d356692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96890 q ha hb
  have h5 (q : Pattern) (ha : d355550 q = 1) (hb : d356693 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d355550, d356693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d355550, d356693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d355572 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d355573 q = 1) (hb : d356694 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d355573, d356694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d355573, d356694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d355574 q = 1) (hb : d356695 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d355574, d356695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d355574, d356695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d355575 q = 1) (hb : d356696 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d355575, d356696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d355575, d356696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d355576 q = 1) (hb : d356697 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d355576, d356697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d355576, d356697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro96998 (p : Pattern) (ha : d355597 p = 1) (hb : d356707 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d355526 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d355535 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d355549 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d355500 q = 1) (hb : d356692 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d355500, d356692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96889 q ha hb
    | true =>
      simp only [d355500, d356692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96890 q ha hb
  have h4 (q : Pattern) (ha : d355550 q = 1) (hb : d356693 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d355550, d356693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d355550, d356693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d355572 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d355573 q = 1) (hb : d356694 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d355573, d356694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d355573, d356694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d355574 q = 1) (hb : d356695 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d355574, d356695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d355574, d356695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d355575 q = 1) (hb : d356696 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d355575, d356696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d355575, d356696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d355582 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d355587 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d355589 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d355510 q = 1) (hb : d356702 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d355510, d356702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96892 q ha hb
    | true =>
      simp only [d355510, d356702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96893 q ha hb
  have h13 (q : Pattern) (ha : d355590 q = 1) (hb : d356703 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d355590, d356703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d355590, d356703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d355593 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d355594 q = 1) (hb : d356704 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d355594, d356704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d355594, d356704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d355595 q = 1) (hb : d356705 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d355595, d356705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d355595, d356705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d355596 q = 1) (hb : d356706 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d355596, d356706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d355596, d356706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d355597 q = 1) (hb : d356707 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d355597, d356707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d355597, d356707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro96999 (p : Pattern) (ha : d355617 p = 1) (hb : d357050 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d355589 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d355510 q = 1) (hb : d356702 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d355510, d356702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96892 q ha hb
    | true =>
      simp only [d355510, d356702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96893 q ha hb
  have h3 (q : Pattern) (ha : d355590 q = 1) (hb : d356703 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d355590, d356703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d355590, d356703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d355593 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d355594 q = 1) (hb : d356704 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d355594, d356704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d355594, d356704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d355615 q = 1) (hb : d356705 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d355615, d356705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d355615, d356705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d355616 q = 1) (hb : d356706 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d355616, d356706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d355616, d356706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d355617 q = 1) (hb : d357050 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d355617, d357050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d355617, d357050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
end NetHack.Soko22Hazard87
